# Independent audit of exceptional primary paths for the actual BBP complement

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
This is Marcel's immutable local question and has no external source URL; none
is invented here.

Audited artifacts:

| artifact | SHA-256 |
|---|---|
| [primary report](bbp_exceptional_path_actual_complement_20260813.md) | `95e3b5d67784adefeda89357b3c652b7dd2b9d2550a26f00dedf2a0f489e01dc` |
| [primary checker](bbp_exceptional_path_actual_complement_20260813_check.py) | `1c151a8cbe253fb6323006f156719a85f970c3eb4b5feed0961e218a59c67b3e` |
| [T74 algebraic core](../../TheoryLib/PiQuantitativeBlockHitting/T74T74ThreePrimaryDecimation.lean) | `eb103c72fd7cf7b0f91c85a102d8d7ed5165028b1d64ae23dac714f6093f2727` |
| [three-primary decimation report](bbp_three_primary_decimation_20260813.md) | `29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0` |
| [all-depth two-adic report](bbp_all_depth_two_adic_attack.md) | `9c1282724c7999fd67133a3f0e756015e564dc6b7a2a1ec44f2efe892b2653d9` |
| [independent two-adic audit](bbp_all_depth_two_adic_independent_audit.md) | `846268c0b45dd82b96c6112054e344669eca62fe9a4308a56e6026f131a25007` |

## Verdict and claim boundary

**PASS with one scope clarification.**  The nine-lift identity, exceptional
fibre count, Haar-measure budget, first Borel--Cantelli conclusion, actual
cross-depth twist, and exact dyadic noncancellation all survive independent
derivation.  The bounded tables also pass a disjoint replay.

The clarification concerns T74.  T74 is `machine-checked` only for four
affine folds, four exponent folds, and four one-term rational decimation
identities.  It explicitly does **not** prove summed three-adic integrality,
the endpoint unit congruence, complementary-coordinate control, or a decimal
word theorem.  The primary report's Section 4 correctly calls T74 merely the
algebraic fold core of the frozen decimation `proof sketch`.  Outcome item 3's
shorter wording, “T74 makes the selected primary characters compatible,” must
be read with that qualification; literally, T74 alone does not establish
the cross-level coefficient congruence.

No mathematical claim is upgraded by this audit.  The elementary all-depth
deductions retain label `proof sketch`, the finite replay retains label
`experiment`, and the bounded source check retains label
`literature-checked`.  CF36, selected-path decay, a fixed-sixteen return, and
canonical V1 all remain `conjecture`s.  There is no `candidate resolution` or
`verified resolution`.

## 1. Normalized target and quantifier check

The canonical V1 statement is

\[
 \forall P\in\mathbb Z_{\ge1}\ \forall k\in\{0,\ldots,10^P-1\}\
 \exists n\in\mathbb Z_{\ge0}:\qquad
 \left\lfloor10^P\{10^n\pi\}\right\rfloor=k.       \tag{IA1}
\]

The integer $k$ is padded to exactly $P$ decimal digits, so leading zeroes
are included.  The existential quantifier asks for one contiguous occurrence.
It does not ask for infinitely many occurrences, normality, an arbitrary
infinite word, or a noncontiguous subsequence.  The exceptional-path report
does not silently exchange any of these readings.

For even $e\ge4$, set

\[
 q_e=3^e,\qquad T_e=3^{e-2},\qquad q_e=9T_e.       \tag{IA2}
\]

For one fixed function $W:\mathbb Z/T_e\mathbb Z\to\mathbb C$, define

\[
 S_e(a;W)=\sum_{j\bmod T_e}e_{q_e}(a10^j)W(j),
 \qquad a\in(\mathbb Z/q_e\mathbb Z)^\times.       \tag{IA3}
\]

The phrase “fixed $W$” is essential: $W$ may change from one epoch to the
next, but it cannot change with $a$ inside the coefficient average.

## 2. Exact nine-lift fibres and counts

For $0\le k<9$, $10^j\equiv1\pmod9$ gives

\[
\begin{aligned}
 e_{q_e}((a+kT_e)10^j)
 &=e_{q_e}(a10^j)e_9(k10^j)\\
 &=e_9(k)e_{q_e}(a10^j).
\end{aligned}                                                    \tag{IA4}
\]

The multiplier is independent of $j$, so for arbitrary complex $W$,

\[
        S_e(a+kT_e;W)=e_9(k)S_e(a;W),\qquad
        |S_e(a+kT_e;W)|=|S_e(a;W)|.                \tag{IA5}
\]

The residues $a+kT_e$ are distinct modulo $q_e$, remain units because
$3\mid T_e$, and are exactly the nine lifts of $a\bmod T_e$.  Conversely,
every unit modulo $q_e$ lies in one such fibre.  Hence

\[
 \#(\mathbb Z/T_e\mathbb Z)^\times={2T_e\over3},\qquad
 9\,{2T_e\over3}=6T_e=\varphi(q_e).                \tag{IA6}
\]

The notation $S_e(b;W)$ for $b$ modulo $T_e$ is therefore harmless only when
it denotes the common **magnitude** of the nine lifts.  It is not a canonical
complex value, because different lifts differ by $e_9(k)$.

At epoch $e+2$, $T_{e+2}=q_e$.  Thus one exceptional coefficient upstairs
indeed brings all nine siblings above its reduction modulo $q_e$ with it.
This is a within-epoch fact using $W_{e+2}$ for all nine siblings.  It gives no
comparison with the downstairs coefficient evaluated against $W_e$.

## 3. GX16, GX17, and the exact EP8 constant

Expanding $|S_e(a;W)|^2$ and averaging over unit $a$ produces a normalized
Ramanujan sum.  For $q=3^e$, it is $1$ when $q$ divides its argument,
$-1/2$ when the argument has exact three-adic valuation $e-1$, and $0$
otherwise.  LTE gives

\[
 v_3(10^d-1)=2+v_3(d).                              \tag{IA7}
\]

On nonzero differences $d\bmod T_e$, the two cases with valuation $e-1$
are precisely $d=T_e/3$ and $d=2T_e/3$.  Therefore, for unit-modulus $W$,

\[
 {1\over\varphi(q_e)}\sum_{3\nmid a}|S_e(a;W)|^2
 =T_e-\operatorname {Re}\sum_{j\bmod T_e}
 W(j+T_e/3)\overline{W(j)}\le2T_e.                \tag{IA8}
\]

Markov's inequality and $\varphi(q_e)=6T_e$ then give

\[
 \#\{a:3\nmid a,\ |S_e(a;W)|\ge\eta T_e\}
 \le {12\over\eta^2}.                              \tag{IA9}
\]

Every bad fibre contains exactly nine coefficients by (IA5), so division by
nine yields exactly the primary report's fibre bound

\[
 \boxed{\#\{\text{bad unit fibres modulo }T_e\}
        \le {4\over3\eta^2}.}                       \tag{IA10}
\]

This argument uses one $W$ within the epoch and says nothing about whether a
bad fibre at epoch $e+2$ was bad at epoch $e$.

## 4. Haar measure and first Borel--Cantelli

Fix in advance one unit-modulus $W_e$ at every even epoch.  For
$a\in\mathbb Z_3^\times$, let $E_e(\eta)$ be the event that its reduction
modulo $q_e$ is bad at threshold $\eta$.  Each unit cylinder modulo $q_e$
has normalized Haar measure

\[
 {1\over\varphi(q_e)}={1\over6T_e}.                 \tag{IA11}
\]

Using (IA9),

\[
 \mu(E_e(\eta))\le{12/\eta^2\over6T_e}
                  ={2\over\eta^2T_e}.              \tag{IA12}
\]

Along $e=4+2r$, $T_e=3^{2+2r}$.  The exact geometric budget is

\[
 \sum_{r\ge0}\mu(E_{4+2r}(\eta))
 \le {2\over\eta^2}\,{1/9\over1-1/9}
 ={1\over4\eta^2}.                                 \tag{IA13}
\]

All events are finite unions of cylinders and hence measurable.  The first
Borel--Cantelli lemma uses only summability, not independence.  For each
fixed $m\ge1$, almost every path is in only finitely many
$E_e(1/m)$.  Intersecting these countably many full-measure sets proves

\[
 \boxed{\text{for Haar-a.e. }a\in\mathbb Z_3^\times,qquad
 {S_e(a\bmod q_e;W_e)\over T_e}\longrightarrow0}   \tag{IA14}
\]

along the even epochs.

Three caveats are indispensable.

1. The sequence $(W_e)$ must be predetermined.  It may be the actual BBP
   sequence after the selected path has been frozen, but the conclusion then
   concerns almost every **alternative** coefficient path.
2. If one instead defines $W_e^{(a)}=F_e/f_{e,a}$ separately for each varied
   coefficient, then $S_e(a;W_e^{(a)})=\sum_jF_e(j)$ for every $a$.  GX16
   cannot average this family because the weight changes with the summation
   variable.  Applying it would be circular.
3. The selected BBP path is one computable element of $\mathbb Z_3^\times$.
   Computable elements form a countable Haar-null set.  A full-measure theorem
   may fail on every computable singleton, so (IA14) does not select this path.

These observations neither prove nor disprove selected-path decay.

## 5. T74 scope and the coefficient nesting premise

Direct inspection of T74 confirms twelve declarations: four affine folds,
four elementary exponent folds, and four rational one-term identities.  The
module header explicitly excludes summed-error integrality, endpoint
instantiation, complementary CRT coordinates, and decimal words.  The twelve
declarations are imported in `TheoryLib.lean` and registered in
`audit/AxiomAudit.lean`; this is the precise `machine-checked` scope.

The stronger endpoint congruence used next comes from the frozen decimation
report's `proof sketch`.  Writing

\[
 \beta_e\equiv3^eB_{M_e}\pmod {3^e},\qquad
 a_e\equiv\beta_e10^{M_e}\pmod {3^e},              \tag{IA15}
\]

that report derives $\beta_{e+2}\equiv\beta_e\pmod {3^e}$.  Also

\[
 M_{e+2}-M_e=5\cdot3^e,qquad
 \operatorname {ord}_{3^e}(10)=3^{e-2}.            \tag{IA16}
\]

The order divides the depth difference, so the claimed coefficient nesting
follows:

\[
                       a_{e+2}\equiv a_e\pmod {3^e}. \tag{IA17}
\]

Equation (IA17) is sound at `proof sketch` level, but it is not a theorem of
T74 by itself.

## 6. EP15 signs and index shifts

Let $q_e=3^e$ and

\[
 f_{e,a}(j)=e_{q_e}(a10^j).
\]

Raising the higher character to the ninth power reduces its modulus from
$3^{e+2}$ to $3^e$.  Using (IA17),

\[
\begin{aligned}
 f_{e+2,a_{e+2}}(j)^9
 &=e_{3^{e+2}}(9a_{e+2}10^j)\\
 &=e_{3^e}(a_{e+2}10^j)\\
 &=e_{3^e}(a_e10^j)=f_{e,a_e}(j).                 \tag{IA18}
\end{aligned}
\]

There is no conjugation or minus sign in (IA18).  The identity actually holds
for every integer $j$; restricting to $0\le j<T_e$ merely identifies the
shared part of the two rows.

## 7. EP16 direct algebra and the changing complement

Put $M=M_e$, $N=M_{e+2}$, and

\[
 \Delta=N-M=5\cdot3^e,qquad N=9M+13.              \tag{IA19}
\]

With

\[
 F_e(j)=e((10^{M+j}-16)B_M),\qquad
 W_e(j)=F_e(j)/f_{e,a_e}(j),                       \tag{IA20}
\]

equation (IA18) cancels the primary character in the ratio.  Its exponent is

\[
\begin{aligned}
 &9(10^{N+j}-16)B_N-(10^{M+j}-16)B_M\\
 &\qquad=10^{M+j}(9\,10^\Delta B_N-B_M)
          +(16B_M-144B_N).                        \tag{IA21}
\end{aligned}
\]

Therefore the exact identity, with both signs checked, is

\[
 \boxed{{W_{e+2}(j)^9\over W_e(j)}
 =e(10^{M+j}D_e+C_e)},                             \tag{IA22}
\]

where

\[
 D_e=9\,10^\Delta B_N-B_M,qquad
 C_e=16B_M-144B_N.                                 \tag{IA23}
\]

The rowwise constant $C_e$ cannot affect a correlation magnitude, but the
$j$-dependent term $10^{M+j}D_e$ cannot be discarded.  The decomposition

\[
 D_e=(9B_N-B_M)+9(10^\Delta-1)B_N                 \tag{IA24}
\]

also confirms three-integrality: the first summand is the frozen decimation
conclusion, while LTE and $v_3(B_N)=-(e+2)$ give

\[
 v_3(9(10^\Delta-1)B_N)=2+(e+2)-(e+2)=2.          \tag{IA25}
\]

Thus the twist is compatible with the three-primary nesting without being
constant in the complementary coordinates.

## 8. EP20 exact dyadic reducedness and no cancellation

The previously independently audited all-depth two-adic `proof sketch`
gives, for every $R\ge1$,

\[
 v_2(B_R)=v_2(R+1)-4R=-K_R,qquad
 K_R=4R-v_2(R+1).                                  \tag{IA26}
\]

This dependency is not part of T74 and is not `machine-checked`.  Given
(IA26), the EP20 deduction is exact.  Since $N=9M+13$ and
$\Delta=N-M=8M+13$,

\[
\begin{aligned}
 (K_N-\Delta)-K_M
 &=3\Delta+v_2(M+1)-v_2(N+1)>0.                  \tag{IA27}
\end{aligned}
\]

For the strict inequality, $v_2(N+1)\le N$ and
$3\Delta-N=15M+26>0$.  The two summands of $D_e$ in (IA23) therefore have
unequal two-adic valuations:

\[
 v_2(9\,10^\Delta B_N)=-(K_N-\Delta)<-K_M=v_2(B_M). \tag{IA28}
\]

The equality case of the non-Archimedean triangle inequality forbids
cancellation of the lower valuation.  Hence, in lowest terms,

\[
 \boxed{v_2(\operatorname {den}D_e)=K_N-\Delta.}   \tag{IA29}
\]

After multiplication by $10^{M+j}$, the active depth is

\[
 K_N-\Delta-M-j.                                   \tag{IA30}
\]

It remains positive throughout $0\le j<T_e$.  A coarse all-depth proof is
obtained from $v_2(N+1)\le N$:

\[
 K_N-\Delta-M-(T_e-1)
 \ge2M+2\Delta-T_e+1>0.                            \tag{IA31}
\]

The exact independent replay gives $1{,}354$ active bits at the last point
of $e=4\to6$ and $12{,}215$ at the last point of $e=6\to8$, matching the
primary report.  Odd-denominator behavior cannot change the exact two-adic
valuation in (IA29).

## 9. Disjoint bounded replay

### `experiment`

The new [independent checker](bbp_exceptional_path_actual_complement_20260813_independent_check.py),
SHA-256
`3b115d0730293ac03bf210ee7b1dec38d34272f6ed178be797db0c7fcc4352f8`,
imports no primary checker.  It differs operationally in the following ways.

- It recomputes each endpoint residue independently at its own modulus
  $3^e$, instead of carrying one top-modulus accumulator.
- It certifies a fresh 60-decimal MPFR shadow of each large phase.
- It reconstructs all $6T_e$ unit coefficients from six cyclic convolutions,
  then independently groups them by reduction modulo $T_e$.
- It checks the two small cross-depth transitions with exact rational and
  modular arithmetic, including the dyadic denominator valuation.
- It replays the five exceptional-set projections and independently checks
  the exact Haar geometric-series budget.

The selected rows agree:

| $e$ | selected $a_e$ | $|S_e|/T_e$ | fibre rank | all-unit rank | maximum $|S_e|/T_e$ |
|---:|---:|---:|---:|---:|---:|
| 4 | 29 | 0.296266113865537 | 4 / 6 | 28--36 / 54 | 0.598344580040705 |
| 6 | 29 | 0.052328658543810 | 46 / 54 | 406--414 / 486 | 0.249570456391329 |
| 8 | 29 | 0.019238483011483 | 359 / 486 | 3,223--3,231 / 4,374 | 0.088641978222574 |
| 10 | 26,273 | 0.011021812372229 | 1,998 / 4,374 | 17,974--17,982 / 39,366 | 0.035839013360416 |
| 12 | 203,420 | 0.004013665889307 | 15,255 / 39,366 | 137,287--137,295 / 354,294 | 0.015008363869177 |
| 14 | 1,797,743 | 0.001184721545067 | 168,116 / 354,294 | 1,513,036--1,513,044 / 3,188,646 | 0.005297625000283 |

The transition counts also agree exactly:

| transition | $\eta$ | higher exceptional units | parent fibres | parents bad below | selected bad lifts |
|:---:|---:|---:|---:|---:|---:|
| 4 to 6 | 0.100 | 234 | 26 | 26 | 0 |
| 6 to 8 | 0.030 | 2,286 | 254 | 244 | 0 |
| 8 to 10 | 0.015 | 8,928 | 992 | 833 | 0 |
| 10 to 12 | 0.007 | 19,458 | 2,162 | 1,586 | 0 |
| 12 to 14 | 0.002 | 381,474 | 42,386 | 33,532 | 0 |

The retained [record](bbp_exceptional_path_actual_complement_20260813_independent_record.txt),
SHA-256
`1e4ee83a41804238b32656d3ebf8466179c69583f7464fca22f977f3a39342f6`,
reports `status=PASS` and exact-record SHA-256
`8e71daa3d7881ebbf0b8ef5ac0f7ad57c67a8a40e98fb668b54b8271ec8198aa`.
The run used 45.29 seconds and 180,712 KB maximum resident memory.  The
primary checker was separately compiled and rerun; it reproduced its frozen
record SHA-256
`9bbdfe2218c537c54216648ca44eaf3d674fda5f51f98986e513cafaa969eae5`
and `status=PASS`.

These computations are finite.  In particular, the decreasing six selected
values are not a rate theorem and do not prove eventual decay.

## 10. Mathlib, literature, and integrity checks

### `literature-checked`

Direct-check date: **2026-08-13 UTC**.

- Mathlib contains the summability-only first Borel--Cantelli theorem as
  `MeasureTheory.measure_limsup_atTop_eq_zero` and the finite-membership form
  `MeasureTheory.ae_finite_setOf_mem` in
  `Mathlib.MeasureTheory.OuterMeasure.BorelCantelli`.  The source explicitly
  distinguishes this from the independence-dependent second lemma.
- The official arXiv records for Joseph Vandehey,
  [*Differencing Methods for Korobov-type Exponential Sums*](https://arxiv.org/abs/1606.07911),
  and Bryce Kerr,
  [*Incomplete exponential sums over exponential functions*](https://arxiv.org/abs/1302.4170),
  study fixed-modulus exponential sums of the form $\sum e_m(ab^n)$ or the
  prime-modulus analogue.  Their advertised scopes do not supply a theorem
  for the synchronized, changing composite-modulus BBP twist (IA22).
- The Bailey--Borwein--Plouffe DOI in the primary report resolves to the AMS
  journal record for the classical BBP paper.  That source supplies the
  four-pole series, not the new exceptional-path conclusions.

This is a bounded applicability check, not an exhaustive novelty search.

All nine relative links in the primary report resolve.  The primary report,
both checkers, the retained record, and T74 are free of forbidden C0 control
bytes.  The primary checker verifies all of its frozen hashes.  This audit
did not edit `ultrapi.md`, Lean, `TheoryLib.lean`, `audit/AxiomAudit.lean`, or
the verification gate, so no new formal-code gate run was required.

## 11. Coordination and final handoff

This audit registered descendant-area watch
`ultrapi-exceptional-path-independent-20260813` on `local:pi-digits` for agent
`codex-ultrapi-exceptional-path-independent`.  Its initial poll was empty at
cursor and delivered sequence 57,488, so no event was acknowledged.
Its final pre-verdict poll was also empty at the same cursor and delivered
sequence, so again no event was acknowledged.  Observation events are
coordination signals only and were not used as mathematical evidence.

The durable positive result is narrow: at each fixed epoch the macroscopic
exceptional coefficients form at most $4/(3\eta^2)$ full nine-lift fibres,
and Haar-almost every predetermined coherent path eventually avoids every
fixed threshold.  The durable obstruction is equally narrow: the actual BBP
path is one deterministic computable singleton, the complements change with
depth, and their exact transition contains the deep nonconstant twist
(IA22).  Neither T74 nor the fibre theorem relates exceptional status across
levels.  A deterministic estimate for the selected path is still missing,
so no pi/V1 promotion is warranted.
