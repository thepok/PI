# Exceptional primary paths for the actual BBP complement

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
This is Marcel's immutable local question and has no external source URL; none
is invented here.

Frozen inputs:

| input | SHA-256 |
|---|---|
| [CF36 Gowers report](bbp_cf36_gowers_cube_persistence_20260813.md) | `3bd9a948945570e975defd7bd2297338da0068f9c82eb027be84364a66bb528e` |
| [independent CF36 audit](bbp_cf36_gowers_cube_persistence_20260813_independent_audit.md) | `46642011eb928e85ed7e707524ed79589c957cf5f1d742db5f0177c3e4887b51` |
| [three-primary decimation](bbp_three_primary_decimation_20260813.md) | `29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0` |
| [complement-Fourier report](bbp_complement_fourier_attack_20260813.md) | `eccb19ffdd7a931cb9de1efb4ab1136ba3f8fb543a84ab00c3e320fd16f2316a` |
| [full-phase endpoint experiment](bbp_three_grid_full_phase_experiment_20260813.md) | `f58f45259f19feb4f2e72f505199ed4476dfdec02bbdb82fbf6892bd6ec80b80` |
| [independent full-phase audit](bbp_three_grid_full_phase_experiment_20260813_independent_audit.md) | `6cd9d451df087ad0208af9f4b02bcd16fbf5af5b0603b36a9bee6c61a0466ed9` |
| [T74 algebraic core](../../TheoryLib/PiQuantitativeBlockHitting/T74T74ThreePrimaryDecimation.lean) | `eb103c72fd7cf7b0f91c85a102d8d7ed5165028b1d64ae23dac714f6093f2727` |

All remained unchanged while this report and its checker were prepared.

## Outcome and claim boundary

Canonical V1 remains a `conjecture`.  This branch proves no estimate for
CF36, no fixed-sixteen return, and no occurrence theorem for every finite
decimal word in pi.

The substantive conclusions have label `proof sketch`.

1. The exceptional-coefficient result GX16--GX17 has an exact ninefold
   refinement.  At epoch $e$, all nine unit lifts of one residue modulo
   $3^{e-2}$ have the same correlation magnitude.  Equivalently, at epoch
   $e+2$, one exceptional coefficient forces all nine siblings above its
   parent modulo $3^e$ to be exceptional.  The exceptional set therefore
   has at most $4/(3\eta^2)$ parent fibres.  This is horizontal branching
   inside one epoch, not persistence along the selected path.
2. For any **predetermined** sequence of unit-modulus weights $W_e$, the
   first Borel--Cantelli lemma turns GX17 into a genuine metric theorem:
   Haar-almost every coherent path in 
   
   \[
                  \mathbb Z_3^\times
   \]
   
   has $S_{a\bmod3^e}(W_e)=o(3^{e-2})$ along the even epochs.  No
   independence between epochs is needed.  This does not select the one BBP
   path; there is no theorem here that it is Haar-generic.
3. The actual four-pole partial sums give an exact cross-depth identity for
   the complements.  T74 makes the selected primary characters compatible,
   but the complement identity is twisted by a nonconstant geometric phase
   whose dyadic denominator remains exponentially deep.  Thus T74 does not
   imply that exceptional status persists, branches forward, or decays.

The bounded FFT diagnostics have label `experiment`.  They independently
reproduce the five preliminary selected magnitudes and maxima through
$e=12$, extend them to $e=14$, and directly show failure of a naive
same-threshold persistence implication on every sampled transition.  The
applicability search is `literature-checked`.  Nothing is promoted to
`machine-checked`, `candidate resolution`, or `verified resolution`.

## 1. Normalized target and actual complement convention

Canonical V1 is

\[
 \forall P\ge1\ \forall 0\le k<10^P\ \exists n\ge0:\qquad
 \left\lfloor10^P\{10^n\pi\}\right\rfloor=k,             \tag{EP1}
\]

where $k$ is represented with exactly $P$ decimal digits, including
leading zeroes.  It asks for one contiguous occurrence of every finite word,
not normality and not infinitely many occurrences.

For even $e\ge4$, put

\[
 q_e=3^e,\qquad T_e=3^{e-2},\qquad
 M_e={5(3^e-1)\over8}-1,\qquad B_e=B_{M_e}.        \tag{EP2}
\]

Let 

\[
 \beta_e\equiv3^eB_e\pmod {3^e},\qquad
 a_e\equiv\beta_e10^{M_e}\pmod {q_e}.             \tag{EP3}
\]

The actual complete-period phase, the varied primary character, and the
actual complement used below are

\[
\begin{aligned}
 F_e(j)&=e\bigl((10^{M_e+j}-16)B_e\bigr),\\
 f_{e,a}(j)&=e_{q_e}(a10^j),\\
 W_e(j)&={F_e(j)\over f_{e,a_e}(j)},
       \qquad 0\le j<T_e.                          \tag{EP4}
\end{aligned}
\]

Thus, with

\[
              S_e(a;W_e)=\sum_{j<T_e}f_{e,a}(j)W_e(j),       \tag{EP5}
\]

the selected value satisfies $S_e(a_e;W_e)=\sum_jF_e(j)$.
The harmless constant primary phase arising from $-16\beta_e$ is absorbed
in $W_e$; it changes no magnitude.  Most importantly, when $a$ is varied
in (EP5), the same fixed $W_e$ is retained.  This is exactly the convention
required by GX16.

## 2. Exact ninefold exceptional fibres

The hypotheses in this section are deliberately single-level.  Fix one
epoch $e$, one arbitrary function

\[
             W:\mathbb Z/T_e\mathbb Z\longrightarrow\mathbb C,           \tag{EP6a}
\]

and use that **same** $W$ in every individual correlation $S_e(a;W)$
from (EP5).  Unit modulus is not even needed for the fibre identity, although
it is needed for the GX16 second-moment bound.  No block energy is being
compared, and no relation between $W_e$ and $W_{e+2}$ is assumed.

Since $q_e=9T_e$ and $10^j\equiv1\pmod9$, every unit $a\bmod q_e$ and
every $0\le k<9$ satisfy

\[
\begin{aligned}
 f_{e,a+kT_e}(j)
 &=e_{q_e}(a10^j)e_{q_e}(kT_e10^j)\\
 &=e_9(k)f_{e,a}(j).
\end{aligned}                                                \tag{EP6}
\]

Consequently

\[
             \boxed{|S_e(a+kT_e;W)|=|S_e(a;W)|}              \tag{EP7}
\]

for every weight $W$, with no BBP hypothesis.  The nine residues
$a+kT_e$ are precisely the nine unit lifts of $a\bmod T_e$.  Combining
(EP7) with GX17 gives

\[
 \#\left\{b\in(\mathbb Z/T_e\mathbb Z)^\times:
       |S_e(b;W)|\ge\eta T_e\right\}
 \le {4\over3\eta^2}.                              \tag{EP8}
\]

Here one representative of a fibre may be used to define the magnitude.
At the next endpoint $T_{e+2}=3^e=q_e$.  Therefore a bad coefficient at
epoch $e+2$ indeed makes all nine of its siblings above one coefficient
modulo $q_e$ bad.  This is the exact branching supplied by the arithmetic.
It costs nine of the $O_\eta(1)$ exceptional slots and does not force that
parent to have been bad at epoch $e$, nor that any child will be bad at
epoch $e+4$.

More explicitly, the word "parent" in the preceding sentence means only the
reduction map

\[
 (\mathbb Z/3^{e+2}\mathbb Z)^\times
       \longrightarrow(\mathbb Z/3^e\mathbb Z)^\times.                  \tag{EP8a}
\]

The nine equal magnitudes upstairs all use $W_{e+2}$.  The downstairs
correlation uses the generally different $W_e$, so (EP7) gives no equality
or inequality between their exceptional sets.  Silently replacing
$W_{e+2}$ by $W_e$ would be exactly the invalid changing-complement
identification that (EP16) later rules out for the actual BBP weights.

## 3. Haar-almost-every coherent path

### `proof sketch`

Fix in advance any unit-modulus weight $W_e:\mathbb Z/T_e\mathbb Z\to
\mathbb C$ for each even $e\ge4$.  It may vary arbitrarily with $e$, but
within an epoch it must be the same function for every varied coefficient.
Let

\[
 E_e(\eta)=\left\{a\in\mathbb Z_3^\times:
 |S_e(a\bmod q_e;W_e)|\ge\eta T_e\right\}.          \tag{EP9}
\]

Normalized Haar measure on 
$\mathbb Z_3^\times$ gives each unit cylinder modulo $q_e$ measure
$1/\varphi(q_e)=1/(6T_e)$.  GX17 therefore gives

\[
 \mu(E_e(\eta))\le {12/\eta^2\over6T_e}
                   ={2\over\eta^2T_e}.             \tag{EP10}
\]

On the even endpoint sequence this is summable, in fact

\[
 \sum_{r\ge0}\mu(E_{4+2r}(\eta))
 \le {2\over\eta^2}\sum_{r\ge0}{1\over3^{2+2r}}
 ={1\over4\eta^2}<\infty.                          \tag{EP11}
\]

The first Borel--Cantelli lemma needs no independence and says that, for
each fixed 
$\eta>0$, Haar-almost every path belongs to only finitely many
$E_e(\eta)$.  Intersecting the full-measure conclusions for the countable
thresholds 
$\eta=1/m$, $m\ge1$, yields

\[
 \boxed{\text{for Haar-a.e. }a\in\mathbb Z_3^\times,\qquad
 {S_e(a\bmod q_e;W_e)\over T_e}\longrightarrow0}            \tag{EP12}
\]

along even $e$.

This is a metric theorem, not a theorem about the selected BBP point.
The actual sequence (EP4) is predetermined once the BBP path $a_e$ is
fixed, so (EP12) legitimately applies to Haar-almost every **alternative**
coherent coefficient path against those frozen weights.  It supplies no
probability law for $a_e$ and no reason that this single deterministic path
lies in the full-measure set.

There is also a computable-singleton separator.  The coherent BBP path is
computable: for each $e$, finite rational four-pole summation and modular
arithmetic compute $\beta_e$ and $a_e$.  The set of computable elements of
$\mathbb Z_3^\times$ is countable and hence Haar-null.  A full-measure
conclusion can therefore fail on every computable path without contradiction.
This does not say that the BBP path fails (EP12); it shows exactly why
Haar-almost-every cannot certify that one computable singleton.

There is a second, sharper caveat.  If one varies $a$ and simultaneously
redefines

\[
                         W_e^{(a)}=F_e/f_{e,a},     \tag{EP13}
\]

then $S_e(a;W_e^{(a)})=\sum_jF_e(j)$ for every $a$.  GX16--GX17 cannot be
applied because the weight is no longer held fixed during the coefficient
average.  Thus it would be circular to use (EP12) to randomize the actual
primary coordinate while recomputing its synchronized complement.

## 4. Actual cross-depth complement identity

Put $M=M_e$, $N=M_{e+2}$, and

\[
        \Delta=N-M=5\cdot3^e,\qquad N=9M+13.       \tag{EP14}
\]

The frozen endpoint decimation report, whose algebraic fold core is
machine-checked in T74, gives 
$a_{e+2}\equiv a_e\pmod {3^e}$.  Hence, on the first $T_e$ exponents,

\[
                     f_{e+2,a_{e+2}}(j)^9=f_{e,a_e}(j).      \tag{EP15}
\]

Unlike the artificial conjugate model, the actual complement has an exact
extra factor.  Direct substitution in (EP4) gives

\[
 \boxed{
 {W_{e+2}(j)^9\over W_e(j)}
 =e\!\left(10^{M+j}D_e+C_e\right),}               \tag{EP16}
\]

where

\[
 D_e=9\,10^\Delta B_{e+2}-B_e,
 \qquad C_e=16B_e-144B_{e+2}.                      \tag{EP17}
\]

The term $C_e$ is constant across the row and is irrelevant to a
correlation magnitude.  The varying term is not removed by T74.  Indeed,

\[
 D_e=(9B_{e+2}-B_e)+9(10^\Delta-1)B_{e+2}.        \tag{EP18}
\]

The first summand is three-integral by the frozen decimation.  LTE gives
$v_3(10^\Delta-1)=e+2$, while
$v_3(B_{e+2})=-(e+2)$; the second summand is also three-integral.
Thus (EP16) is compatible with the primary ninth-root relation.

It remains highly nontrivial in the complementary directions.  Let

\[
                  K_R=4R-v_2(R+1)                 \tag{EP19}
\]

be the exact dyadic denominator exponent of $B_R$.  Since
$K_N-\Delta>K_M$, reducedness shows exactly

\[
                  v_2(\operatorname {den}D_e)=K_N-\Delta.   \tag{EP20}
\]

After multiplication by $10^{M+j}$, its varying dyadic depth is

\[
                  K_N-\Delta-M-j>0\qquad(0\le j<T_e).       \tag{EP21}
\]

This tends linearly to infinity with $M$.  The bounded exact replay gives
minimum depths 1,354 and 12,215 bits on the transitions
$e=4\to6$ and $6\to8$.  Formula (EP16), not the untwisted identity
$W_{e+2}^9=W_e$, is the actual four-pole cross-depth law.

Equations (EP16)--(EP21) do not prove that the twist cancels; they also do
not permit an exceptional correlation to be transported unchanged.  They
isolate the missing theorem: one needs phase-sensitive cancellation for this
specific growing dyadic/odd CRT twist, or a direct argument that the selected
path eventually avoids the bounded exceptional fibres.

## 5. All-unit diagnostic on the actual rows

### `experiment`

The checker evaluates all $\varphi(3^e)=6T_e$ unit coefficients without a
quadratic loop.  The units are six cosets of the cyclic subgroup generated by
ten, so six cyclic FFT correlations give every value.  Equation (EP7) then
groups them into $\varphi(T_e)=2T_e/3$ distinct magnitude fibres.  Ranks in
the table are fibre ranks; the all-unit rank interval is the corresponding
nine-way tie.

| $e$ | $M_e$ | $T_e$ | selected $a_e$ | selected $\lvert S_e\rvert/T_e$ | fibre rank | all-unit rank | maximum $\lvert S_e\rvert/T_e$ |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 4 | 49 | 9 | 29 | 0.296266113866 | 4 / 6 | 28--36 / 54 | 0.598344580041 |
| 6 | 454 | 81 | 29 | 0.052328658544 | 46 / 54 | 406--414 / 486 | 0.249570456391 |
| 8 | 4,099 | 729 | 29 | 0.019238483011 | 359 / 486 | 3,223--3,231 / 4,374 | 0.088641978223 |
| 10 | 36,904 | 6,561 | 26,273 | 0.011021812372 | 1,998 / 4,374 | 17,974--17,982 / 39,366 | 0.035839013360 |
| 12 | 332,149 | 59,049 | 203,420 | 0.004013665889 | 15,255 / 39,366 | 137,287--137,295 / 354,294 | 0.015008363869 |
| 14 | 2,989,354 | 531,441 | 1,797,743 | 0.001184721545 | 168,116 / 354,294 | 1,513,036--1,513,044 / 3,188,646 | 0.005297625000 |

The first five selected magnitudes and maxima independently reproduce the
values proposed in the task; the $e=14$ row is new finite data.  The
selected values have random-scale diagnostics
$\sqrt{T_e}|S_e|/T_e=0.889,0.471,0.519,0.893,0.975,0.864$.
This pattern is suggestive but is neither a rate theorem nor a curve fit.

The actual transition test is equally informative.  For each row below, the
selected parent is above the displayed threshold and all nine selected lifts
at the next endpoint are below it.  `Higher exceptional` counts coefficients;
`parents` divides those coefficients into exact ninefold fibres; `overlap`
counts parents whose lower-epoch magnitude is also above the same threshold.

| transition | $\eta$ | lower selected | upper selected | higher exceptional | parents | overlap | selected lifts |
|:---:|---:|---:|---:|---:|---:|---:|---:|
| 4 to 6 | 0.100 | 0.296266 | 0.052329 | 234 | 26 | 26 | 0 |
| 6 to 8 | 0.030 | 0.052329 | 0.019238 | 2,286 | 254 | 244 | 0 |
| 8 to 10 | 0.015 | 0.019238 | 0.011022 | 8,928 | 992 | 833 | 0 |
| 10 to 12 | 0.007 | 0.011022 | 0.004014 | 19,458 | 2,162 | 1,586 | 0 |
| 12 to 14 | 0.002 | 0.004014 | 0.001185 | 381,474 | 42,386 | 33,532 | 0 |

The changing thresholds make the five-row display only an `experiment`.
Already the first transition at the fixed threshold $\eta=0.1$ refutes the
literal implication "selected bad at $e$ implies a selected bad lift at
$e+2$" for the actual sampled rows.  Conversely, incomplete overlap shows
that higher exceptional fibres need not project to lower exceptional fibres.
Neither finite observation proves eventual decay.

For $e=4,6,8$, the four-pole sums and complete phase streams are exact
`Fraction` values.  For $e=10,12,14$, a 50-decimal phase stream is extracted
from a pi prefix whose two directed MPFR endpoint computations have identical
integer floors.  The positive BBP-tail bound is below $10^{-900}$ already
on the $e=10$ complete period.  The FFT itself is ordinary binary complex
arithmetic and is deliberately retained only as an `experiment`; no directed
FFT enclosure is claimed.

## 6. Reproduction and frozen record

The standalone
[checker](bbp_exceptional_path_actual_complement_20260813_check.py), SHA-256
`1c151a8cbe253fb6323006f156719a85f970c3eb4b5feed0961e218a59c67b3e`,
imports no branch checker.  It verifies every frozen hash; recomputes all six
endpoint units directly from the four-pole coefficient through depth
2,989,354; checks all unit fibres and ranks; replays GX16 on every actual row;
records 60 exceptional-set projections; checks the exact cross-depth rational
identity at 90 points on the first two transitions; and verifies the exact
geometric-series budget in (EP11) for the first twelve rational thresholds.

Run from the repository root:

```text
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_exceptional_path_actual_complement_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_exceptional_path_actual_complement_20260813_check.py
```

The retained run used about 151 MB maximum resident memory and 43 seconds.  It
reported:

```text
status=PASS
projection_records=60
cross_depth_exact_transitions=2
borel_cantelli_even_epoch_sum_eta_inverse_m=m^2/4
asserts_selected_bbp_path_is_haar_generic=false
exact_record_sha256=9bbdfe2218c537c54216648ca44eaf3d674fda5f51f98986e513cafaa969eae5
asserts_cf36_bound=false
asserts_path_decay=false
asserts_fixed_return=false
asserts_v1=false
```

## 7. Mathlib and primary-literature applicability

### `literature-checked`

Search and direct-check date: **2026-08-13 UTC**.

- The local mathlib search found the first Borel--Cantelli lemma exactly as
  `MeasureTheory.measure_limsup_atTop_eq_zero` in
  `Mathlib.MeasureTheory.OuterMeasure.BorelCantelli`.  Its summability-only
  form confirms that (EP12) needs no inter-epoch independence.  No new formal
  infrastructure was introduced in this branch.
- Bailey--Borwein--Plouffe,
  [*On the Rapid Computation of Various Polylogarithmic Constants*](https://doi.org/10.1090/S0025-5718-97-00856-9),
  supplies the four-pole series defining $B_M$.  It does not give (EP12),
  a deterministic exceptional-path theorem, decimal distribution, or V1.
- Joseph Vandehey,
  [*Differencing Methods for Korobov-type Exponential Sums*](https://arxiv.org/abs/1606.07911),
  and Bryce Kerr,
  [*Incomplete exponential sums over exponential functions*](https://arxiv.org/abs/1302.4170),
  were rechecked for the geometric phase in (EP16).  Their nontrivial ranges
  and fixed-modulus/local hypotheses do not estimate this logarithmic-length,
  synchronized composite-modulus complement; the detailed applicability
  boundaries remain those in the frozen complement-Fourier report.

This is a bounded applicability record, not an exhaustive search or a novelty
claim.  The Borel--Cantelli deduction is classical; the ninefold fibre and
cross-depth identities are elementary deductions from the frozen arithmetic.

## 8. Coordination record and sharp handoff

This branch registered descendant-area watch
`ultrapi-exceptional-path-20260813` on `local:pi-digits` for agent
`codex-ultrapi-exceptional-path`.  Its initial poll was empty at cursor and
delivered sequence 57,475, so no event was acknowledged.  Observation events
are coordination signals only and were not used as mathematical evidence.

The positive result is now exact: every macroscopic exceptional coefficient
branches into a full nine-sibling fibre, and Haar-almost every predetermined
coherent path eventually avoids every fixed macroscopic threshold.  The
negative result is equally exact: this metric theorem cannot select the BBP
path, and the actual four-pole complement crosses depths through the deep twist
(EP16), not through an untwisted ninth-root recurrence.

The remaining target is therefore deterministic and sharply isolated: prove
that the specific BBP lift $a_e$ avoids the $O_\eta(1)$ exceptional fibres
for every fixed $\eta>0$, or estimate its selected relative correlation
directly.  No such estimate is obtained here, so CF36 and canonical V1 remain
`conjecture`s.
