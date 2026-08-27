# Independent audit of BBP growing-band joint harmonics

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
This is Marcel's immutable local question and has no external source URL; none
is invented here.

Audited artifacts:

| artifact | SHA-256 |
|---|---|
| [primary report](bbp_growing_band_joint_harmonic_20260813.md) | `e44096cba88629cce55668332096c22f14950ff9e6c209cdd6b0a1cd36c776b6` |
| [primary checker](bbp_growing_band_joint_harmonic_20260813_check.py) | `edd7cdb4971b3969aaa05f3764036f7ad78cfecfe1a5362c9d5e1a00b981b30b` |
| [Peres--Yang endpoint report](peres_yang_bbp_endpoint_attack_20260813.md) | `3721a8e1a43fd3c4244ab8ffa11e0da0581e169d037cdf04f85e18ec1a539b60` |
| [independent Peres--Yang audit](peres_yang_bbp_endpoint_attack_20260813_independent_audit.md) | `8c138103b4b2afb3e2b6e559c147c9b1ed69495e3689c1d00fa9fe50cee062ff` |

## Verdict and claim boundary

**PASS with two scope clarifications.**  Equations underlying 40fe, 40ff,
and 40fg are correct.  The ten actual histograms, their integer Fourier
energies, the isospectral empty histogram, and all six primary-preserving
countermodels survive a disjoint replay.

The first clarification concerns the phrase “Ramanujan averaging controls a
horizontal slice.”  The frozen selected-**unit** theorem averages only over
$b\in(\mathbb Z/3^e\mathbb Z)^\times$ on one complete $T=3^{e-2}$
period.  The growing-band row has length $L$ rather than $T$, and many of its
$h$ are divisible by three, so $b=ha$ is then not a unit.  The claimed
horizontal-slice statement remains true if one instead averages over **all**
$b\bmod3^e$; elementary additive orthogonality gives an exact collision
second moment for the actual $L$-point row.  It must not be attributed
literally to the frozen unit theorem for the whole band.

The second clarification concerns the artificial complement in Section 3.
The fixed complement
$W_n=\overline{e_{3^e}(aR_n)}$ makes
$W_n^h=\overline{e_{3^e}(haR_n)}$ and hence produces $S_h=L$ for every
$h$.  If “on every slice” is read as a different artificial weight allowed
for each independently varied $b$, that would invalidate the averaging.  The
valid no-go uses this one fixed base sequence and only the diagonal
$b=ha$.

No result is promoted by this audit.  The analytic deductions retain label
`proof sketch`, the bounded replay retains label `experiment`, and the dated
applicability review retains label `literature-checked`.  A growing-band
bound, endpoint gap law, fixed-sixteen return, and canonical V1 all remain
`conjecture`s.  There is no `candidate resolution` or `verified resolution`.

## 1. Normalized target and bandwidth quantifiers

Canonical V1 is

\[
 \forall P\in\mathbb Z_{\ge1}\ \forall k\in\{0,\ldots,10^P-1\}\
 \exists n\in\mathbb Z_{\ge0}:\qquad
 \left\lfloor10^P\{10^n\pi\}\right\rfloor=k,       \tag{IA1}
\]

with $k$ padded to exactly $P$ digits.  It asks for one contiguous occurrence
of every finite word, not normality, infinite recurrence, or an arbitrary
infinite string.

For one row $x_1,\ldots,x_L\in[0,1)$ and an integer $K\ge2$, define

\[
 q_n=\lfloor Kx_n\rfloor,\qquad
 c_a=\#\{n:q_n=a\},\qquad 0\le a<K.                \tag{IA2}
\]

The finite experiments use $K=\lfloor L/\log L\rfloor$.  A sharp
constant-one gap upper bound would require roughly
$K=2L/((1+\varepsilon)\log L)$ because hitting all $K$ cells gives maximum
gap at most $2/K$.  The report explicitly records this factor two; it does
not silently claim the finite bandwidth has the sharp constant.

## 2. Exact cell inversion and coverage event

Let $\zeta=e^{2\pi i/K}$ and

\[
 C_h=\sum_{n=1}^L\zeta^{hq_n},\qquad
 F_a=\sum_{h=1}^{K-1}C_h\zeta^{-ha}.               \tag{IA3}
\]

Finite character orthogonality gives

\[
\begin{aligned}
 L+F_a
 &=\sum_{h=0}^{K-1}\sum_n\zeta^{h(q_n-a)}\\
 &=\sum_n K\,\mathbf1_{q_n=a}=Kc_a.               \tag{IA4}
\end{aligned}
\]

Thus $F_a=Kc_a-L$ is real and

\[
 \text{all cells occupied}
 \iff \min_aF_a>-L.                                \tag{IA5}
\]

The inequality is strict: an empty cell gives $F_a=-L$, while every occupied
cell has integer margin $F_a+L=Kc_a\ge K$.

## 3. Quantization identity and 40fe

Put $z_n=e(x_n)$ and $\theta_n=\{Kx_n\}$.  Since
$Kx_n=q_n+\theta_n$,

\[
 \zeta^{q_n}=e(q_n/K)=e(x_n)e(-\theta_n/K).        \tag{IA6}
\]

If $z_n=e_{3^e}(aR_n)W_n$, raising (IA6) to $h$ and summing gives exactly

\[
 C_h=\sum_n e_{3^e}(haR_n)W_n^h
                  e(-h\theta_n/K).                 \tag{IA7}
\]

The triangle inequality and
$|e(-u)-1|=2|\sin\pi u|\le\min(2,2\pi|u|)$ yield

\[
 \boxed{\left|C_h-\sum_nz_n^h\right|
 \le L\min\!\left(2,{2\pi|h|\over K}\right).}    \tag{IA8}
\]

For the report's range $1\le h<K$, the displayed formula with $h$ instead of
$|h|$ is correct.  At $h\asymp K$, this is only an $O(L)$ estimate.  The
factor $e(-h\theta_n/K)$ depends on the complete $x_n$, so it cannot be
assigned to either CRT side independently.  Summing the pointwise upper bound
over the band can only lose more; no small-rounding transfer is available.

The independent checker cross-multiplies (IA6) exactly at all 1,882 points of
the six rational rows.  No floating complex equality is used for this check.

## 4. Exact diagonal selection and the unit-slice caveat

For the unquantized powers define

\[
 \mathcal T(h,b)=\sum_ne_{3^e}(bR_n)W_n^h.         \tag{IA9}
\]

The actual sum is the single diagonal value

\[
 \boxed{S_h=\sum_nz_n^h=\mathcal T(h,ha).}         \tag{IA10}
\]

This is just $(uv)^h=u^hv^h$ and is valid whether or not $3\mid h$.
What averaging theorem applies depends on the domain of $b$.

For all residues $b\bmod q$, $q=3^e$, additive orthogonality gives the exact
weighted-collision identity

\[
 {1\over q}\sum_{b\bmod q}|\mathcal T(h,b)|^2
 =\sum_{r\bmod q}\left|
   \sum_{n:R_n\equiv r\ (q)}W_n^h\right|^2
 \le\#\{(m,n):R_m\equiv R_n\pmod q\}.             \tag{IA11}
\]

On the endpoint power orbit, the residue period is $T=3^{e-2}$, so the right
side is at most $L\lceil L/T\rceil$.  Consequently each horizontal slice has
at most

\[
 {\lceil L/T\rceil\over\eta^2L}                   \tag{IA12}
\]

of all additive coefficients with magnitude at least $\eta L$.  This is a
genuine horizontal average.  Since $q=9T$ and $L\asymp T$ on these endpoint
rows, it gives $O_\eta(1)$ exceptional $b$ on each slice.  It does not
restrict the varying diagonal $b=ha$ across $K$ different slices.

For $3\nmid h$, $ha$ is a unit, but the sharper frozen unit-Ramanujan theorem
is stated for one complete $T$-point period, not directly for the present
$L$-point row.  For $3\mid h$, there is the additional obstruction that
$ha$ is nonunit.  Among $1\le h<K$, roughly one third lie in this latter
class.  The primary report's logic survives through (IA11), but the frozen
selected-unit theorem is only an analogy here unless a separate truncation or
stratified transfer is supplied.

The fixed artificial sequence

\[
                     W_n=\overline{e_{3^e}(aR_n)} \tag{IA13}
\]

obeys $W_n^h=\overline{e_{3^e}(haR_n)}$ and hence
$\mathcal T(h,ha)=L$ for every $h$.  It is not asserted to be the BBP
complement.  It proves only that separate horizontal moment bounds do not
select one adversarial diagonal point on each slice.

Finally, for arbitrary $\lambda_h$,

\[
 \sum_h\lambda_hS_h=\sum_n\sum_h\lambda_hz_n^h,   \tag{IA14}
\]

and the analogous quadratic combination depends on
$(z_m\overline z_n)^h$.  Joint summation therefore reconstructs polynomials
and pair spacings of the **full** points; it does not manufacture independent
local CRT savings.

## 5. Large-sieve and spacing scope

The classical large sieve controls values of a trigonometric polynomial at
well-separated full frequencies.  Here equal cell labels intentionally
collide, and distinct rational phases with complete denominator $D$ have only
the elementary spacing $\ge1/D$.  Since $D$ is exponentially large while
$K$ is of row-length scale, this is vastly smaller than $1/K$.  Separation of
the three-primary projection does not imply separation of the full phases:
the complementary coordinate can cancel it.  Thus applying a dual large
sieve after (IA14) merely returns the full-spacing problem and supplies no
growing-band theorem.

## 6. Parseval, energy, and the signed event

Parseval applied to (IA4) yields

\[
 E_K:=\sum_{h=1}^{K-1}|C_h|^2
     =K\sum_ac_a^2-L^2.                            \tag{IA15}
\]

If one cell is empty, Cauchy--Schwarz over the remaining $K-1$ cells gives

\[
 \sum_ac_a^2\ge{L^2\over K-1},\qquad
 E_K\ge{L^2\over K-1}.                            \tag{IA16}
\]

The strict reverse is sufficient for coverage, but not necessary.  For
$L=93$, $K=20$, the actual covered pre-drop row has $E_K=1211$.  The empty
histogram

\[
                     (6^6,5^{11},1^2,0)            \tag{IA17}
\]

also has total 93 and exact energy

\[
 20(6\cdot6^2+11\cdot5^2+2\cdot1^2)-93^2=1211.   \tag{IA18}
\]

Thus even identical scalar energy cannot decide coverage.  Likewise a
symmetric bound $\max_a|F_a|<L$ is only sufficient.  It is false on the
covered $e=8,10,12$ rows because their positive peaks exceed $L$.

## 7. The exact e12 trough and 40fg

Both $e=12$ rows have

\[
 L=67799,qquad K=6094,qquad\min_ac_a=1.           \tag{IA19}
\]

Using (IA4),

\[
 \boxed{\min_a(Kc_a-L)=K-L=-61705=-L+K.}          \tag{IA20}
\]

The forbidden boundary is $-L=-67799$, so the exact safety margin is $K$.
This rederives 40fg without a complex DFT.  A **uniform** approximation with
one-sided error strictly smaller than $K$ would preserve positivity of the
least cell.  A statement merely of size $o(L)$ does not logically provide
that: for example $L/(\log L)^{1/2}=o(L)$ but is much larger than
$K\asymp L/\log L$.  The report correctly leaves open a one-sided
exponential-moment/minorant argument or an exact nonvanishing mechanism.

The phrase “near-boundary regime” is relative to the growing-band scale: the
normalized margin $K/L\sim1/\log L$ tends to zero.  This one finite row alone
does not establish that such a regime persists asymptotically.

## 8. All six primary-preserving countermodels

For an exact row write

\[
 B_M={P\over D},\qquad D=3^EC,qquad(3,C)=1.       \tag{IA21}
\]

Let $r=P\bmod3^E$ and choose the least $t\ge0$ such that

\[
                       P'=r+t3^E,qquad(P',D)=1.   \tag{IA22}
\]

Then $P'/D$ has the same complete reduced denominator, and its additive
three-primary coordinate is unchanged:

\[
 P'C^{-1}\equiv PC^{-1}\pmod {3^E}.               \tag{IA23}
\]

Hence every projected primary phase and the complete primary grid agree.
The complementary coordinates generally change; in particular, $P'$ is not
congruent to $P\pmod D$.  The six independently recomputed cases are:

| ambient $e$ | row | $M$ | $E$ | $K$ | primary period | $t$ | $P'$ | full row arc |
|---:|:---:|---:|---:|---:|---:|---:|---:|:---:|
| 4 | pre-drop | 49 | 4 | 4 | 9 | 7 | 617 | $<10^{-126}$ |
| 4 | first-drop | 50 | 3 | 4 | 3 | 9 | 263 | $<10^{-129}$ |
| 6 | pre-drop | 454 | 6 | 20 | 81 | 4 | 3307 | $<10^{-1183}$ |
| 6 | first-drop | 455 | 5 | 20 | 27 | 14 | 3547 | $<10^{-1185}$ |
| 8 | pre-drop | 4099 | 8 | 124 | 729 | 12 | 79039 | $<10^{-10676}$ |
| 8 | first-drop | 4100 | 7 | 124 | 243 | 11 | 26171 | $<10^{-10682}$ |

For every listed exponent $n$, the rational phase
$(10^n-16)P'/D$ lies strictly between zero and $1/K$, so every quantized label
is exactly zero.  The row misses all $K-1$ other cells.  Since
$K<M<p$ for every high denominator prime $p>M$, $h<K$ implies $p\nmid h$;
combined with $(P',D)=1$, the local multiplier remains primitive at every
such prime.  This does not prevent global CRT cancellation.

These six rows are `experiment`s and information-scope countermodels.  They
are not BBP truncations, not counterexamples to V1, and do not show the actual
BBP numerator collapses.  They only prove that the preserved primary grid,
denominator size, coprimality, local primitivity, and power law $W^h$ do not
determine the desired coverage.

## 9. Disjoint replay

### `experiment`

The new [independent checker](bbp_growing_band_joint_harmonic_20260813_independent_check.py),
SHA-256
`d9083af5009f7953f5e262daa2899f69293b95122a723e9327de9eb210443d86`,
imports no primary checker.  It uses the literal four-pole BBP summands, a
fresh 70-decimal directed MPFR shadow, a separate Decimal computation of
$\lfloor L/\log L\rfloor$, exact integer occupancies, and exact modular CRT
checks.  It independently reproduces:

- all ten actual rows and both $e=12$ margins;
- eight failures of the sufficient energy certificate;
- six failures of the sufficient symmetric sup-norm certificate;
- the empty energy-1211 histogram;
- all six collapsed rows, complete primary periods, least coprime lifts, and
  microscopic arc exponents;
- 1,882 exact rational quantization identities and six exact diagonal/CRT
  rows.

The retained [record](bbp_growing_band_joint_harmonic_20260813_independent_record.txt),
SHA-256
`ba497c805aa9bb446106ef0159f29629d45a265471bf92a7513dbceab3f8d8f6`,
reports `status=PASS` and exact-record SHA-256
`3212a0030910842034d223bf495077502306bd8e2e63d7b7539a2558857db3b3`.
The retained run used 48.28 seconds and 47,728 KB maximum resident memory.

The primary checker was separately compiled and rerun.  It reported
`status=PASS`, reproduced exact-record SHA-256
`cc2cdf5824f772cc8062205f661ea605e244f369100132f1820f70fd481648c6`,
and used 8.90 seconds and 59,848 KB maximum resident memory.

Finite agreement supplies no asymptotic gap theorem or trend certificate.

## 10. Mathlib and literature applicability

### `literature-checked`

Direct-check date: **2026-08-13 UTC**.

- Mathlib provides finite-character orthogonality.  The repository already
  specializes it in
  `TheoryLib/PiPositiveDecimalFactorEntropy/T3FiniteFourierObstruction.lean`,
  including `finiteFourier_parseval` and a support/energy lower bound.  These
  ingredients formalize the symmetric information in (IA15)--(IA16), not the
  missing selected negative-trough estimate.
- The repository's `T61T61VaalerAnalytic.lean` proves an explicit periodic
  Vaaler **majorant**, including endpoint values, and T108 explicitly records
  that its proved direction is incidence $\le$ majorant.  It does not contain
  the endpoint-safe interval minorant or the growing-band selected BBP
  harmonic estimate needed here.
- Jeffrey Vaaler's
  [*Some Extremal Functions in Fourier Analysis*](https://doi.org/10.1090/S0273-0979-1985-15349-2)
  is a primary source for band-limited extremal functions.  It supplies the
  general minorant technology, not a bound for the actual diagonal family
  (IA10).
- Montgomery--Vaughan,
  [*The Large Sieve*](https://doi.org/10.1112/S0025579300004708), controls
  trigonometric polynomials at separated full frequencies.  It does not allow
  three-primary separation to replace separation of the complete BBP phases.

The primary report itself contains no literature section and makes no
`literature-checked` claim.  This audit's dated search is a bounded
applicability check, not an exhaustive novelty search.

All seven relative links in the primary report resolve.  The primary report,
both checkers, the retained record, and this audit are free of forbidden C0
control bytes.  The primary checker verifies every frozen input hash.  This
branch did not edit `ultrapi.md`, Lean, `TheoryLib.lean`,
`audit/AxiomAudit.lean`, or the verification gate, so no formal-code gate run
was required.

## 11. Coordination and final handoff

This audit registered descendant-area watch
`ultrapi-growing-band-independent-20260813` on `local:pi-digits` for agent
`codex-ultrapi-growing-band-independent`.  Its initial poll was empty at
cursor and delivered sequence 57,499, so no event was acknowledged.  Its
final pre-verdict poll was also empty at the same cursor and delivered
sequence, so again no event was acknowledged.  Observation events are
coordination signals only and were not used as mathematical evidence.

The durable conclusion is a method boundary, not a pi theorem.  Quantization
adds a full-phase factor of $O(L)$ size at growing harmonics; removing it puts
the actual data on an unselected diagonal; scalar energy and symmetric
moments erase the sign required for cell occupancy; and the six exact
countermodels show that the primary grid plus local primitivity cannot select
the actual complementary numerator.  The missing result remains a one-sided,
uniform, selected-numerator bound with error below the $L/\log L$ cell
margin, or an exact nonvanishing theorem.  Neither is obtained here.
