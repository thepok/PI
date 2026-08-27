# T29: Fixed-seed inverse-limit audit

Status: `proof sketch`

## Provenance and scope

- Agenda item: T29, serving G5.
- Canonical local statement: `knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt`.
- Canonical statement SHA-256:
  `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.
- Original source URL: none is recorded; the canonical question was formulated
  locally by this system on 2026-07-22.
- Kernel-checked input used in Section 8:
  `TheoryLib.PiPositiveDecimalFactorEntropy.T28T28ScaleDependentDecimalOrbit`,
  SHA-256
  `58652b80b1b3fa6facab3a8169a2e2b1076d9f7fcb8415558ceedf4ee0216a81`,
  especially
  `DecimalFactorComplexity.ScaleDependentDecimalOrbit.orbitLabel_eq_natCast`
  and
  `DecimalFactorComplexity.ScaleDependentDecimalOrbit.family_parameters`.

This note concerns an abstract fixed circle seed and floor quantization. It
does not concern the value of pi. It makes no conclusion about decimal factor
entropy, amplification, C7, or C1.

## 1. Normalized question and quantifiers

Write `N_+ = {1,2,3,...}` and `N_0 = {0,1,2,...}`. Fix the explicit modulus
chain

\[
  q_s=9\cdot 30^s \qquad (s\in N_+).
\]

Thus, for `t >= s`,

\[
  q_t/q_s=30^{t-s}\in N_+,
  \qquad q_s\mid q_t,
  \qquad \lim_{s\to\infty}q_s=\infty.
\]

The data to be audited are integers

\[
  a_{s,j}\in\{0,1,\ldots,q_s-1\}
  \qquad(s\in N_+,\ j\in N_0).
\]

The question is exactly when there is one `x in [0,1)` such that

\[
  a_{s,j}=\left\lfloor q_s\{10^j x\}\right\rfloor
  \quad\hbox{for every }s\in N_+,\ j\in N_0.             \tag{1.1}
\]

Here `{u}=u-floor(u)` is always the representative in `[0,1)`. Equivalently,
`x` represents one seed in the circle `R/Z`. The same `x` must work at every
scale and every time.

The possible ambiguities are resolved as follows.

1. Scale compatibility is required for every pair `t >= s`, not merely along
   a selected subsequence.
2. Successors are linear in time: they relate `j` to `j+1` for every
   `j in N_0`; there is no wrap from a finite last index back to zero.
3. Quantization cells are left closed and right open. This convention is
   essential at decimal and circle boundaries.
4. The digit error may depend on both `s` and `j`. No cross-scale equality of
   digit errors is assumed.
5. Every supremum below ranges over all positive scales.

## 2. Coarse projections and cells

For `t >= s`, put `r_{t,s}=q_t/q_s=30^(t-s)` and define the coarse projection

\[
  P_{t\to s}:\{0,\ldots,q_t-1\}\longrightarrow
      \{0,\ldots,q_s-1\},
  \qquad
  P_{t\to s}(a)=\left\lfloor\frac{a}{r_{t,s}}\right\rfloor.       \tag{2.1}
\]

This is the projection between floor cells, not reduction modulo `q_s`.
Indeed, the label `a` denotes the half-open interval

\[
  C_q(a)=[a/q,(a+1)/q)\subset[0,1).                              \tag{2.2}
\]

Writing `a=r_{t,s}b+c`, where `0 <= c < r_{t,s}`, shows

\[
  P_{t\to s}(a)=b
  \quad\hbox{and}\quad
  C_{q_t}(a)\subset C_{q_s}(b).                                  \tag{2.3}
\]

The projections compose: for `u >= t >= s`, Euclidean division, or the
nesting of the aligned cells, gives

\[
  P_{u\to s}=P_{t\to s}\circ P_{u\to t}.                         \tag{2.4}
\]

**Projection compatibility (PC).** For every `j in N_0` and every
`t >= s >= 1`, require

\[
  P_{t\to s}(a_{t,j})=a_{s,j}.                                   \tag{PC}
\]

For fixed `j`, define

\[
  \ell_{s,j}=a_{s,j}/q_s,
  \qquad
  u_{s,j}=(a_{s,j}+1)/q_s,
  \qquad
  I_{s,j}=[\ell_{s,j},u_{s,j}).                                  \tag{2.5}
\]

Under (PC), equation (2.3) says that `I_{t,j} subset I_{s,j}` whenever
`t >= s`. In particular, the lower endpoints are nondecreasing and the upper
endpoints are nonincreasing as the scale is refined.

## 3. The boundary and successor conditions

Nested *closed* cells of shrinking diameter would automatically meet. These
cells are right open, so compatibility alone does not guarantee a point in
their intersection. The required condition is the following.

**Boundary condition (BC).** For every `j in N_0`, let

\[
  L_j=\sup_{t\in N_+}\frac{a_{t,j}}{q_t}.                         \tag{3.1}
\]

The supremum exists because all terms lie in `[0,1)`. Require, for every
`s in N_+` and `j in N_0`,

\[
  L_j<\frac{a_{s,j}+1}{q_s}.                                     \tag{BC}
\]

Thus `L_j` is not an excluded right endpoint at any finite scale. Notice that
(BC) is a quantified strict inequality, not merely the assertion `L_j <= 1`.

**Digit-successor condition (DS).** For every `s in N_+` and `j in N_0`,
there is an integer `e_{s,j}` such that

\[
  0\le e_{s,j}\le9,
  \qquad
  a_{s,j+1}\equiv 10a_{s,j}+e_{s,j}\pmod {q_s}.                  \tag{DS}
\]

The error is an ordinary base-ten digit. The congruence is the appropriate
condition because multiplication by ten takes place on the circle.

## 4. Two elementary floor identities

We record the exact facts used in the proof.

**Lemma 4.1 (projection of a floor).** If `r,q` are positive integers and
`0 <= y < 1`, then

\[
  \left\lfloor\frac{\lfloor rqy\rfloor}{r}\right\rfloor
  =\lfloor qy\rfloor.                                            \tag{4.1}
\]

*Proof.* Put `m=floor(qy)` and write `qy=m+theta` with `0 <= theta < 1`.
Then `floor(rqy)=rm+floor(r theta)`, where `0 <= floor(r theta)<r`.
Dividing by `r` and taking the floor gives `m`. `square`

**Lemma 4.2 (one-scale decimal successor).** Let `q` be a positive integer,
`0 <= y < 1`,

\[
  a=\lfloor qy\rfloor,
  \qquad b=\lfloor q\{10y\}\rfloor.
\]

Then, for

\[
  e=\left\lfloor10\{qy\}\right\rfloor\in\{0,\ldots,9\},       \tag{4.2}
\]

one has

\[
  b\equiv10a+e\pmod q.                                           \tag{4.3}
\]

*Proof.* Since `qy=a+{qy}`,

\[
  \lfloor10qy\rfloor=10a+\lfloor10\{qy\}\rfloor=10a+e.
\]

Also

\[
  q\{10y\}=10qy-q\lfloor10y\rfloor,
\]

and `q floor(10y)` is an integer. Taking floors proves that `b` differs from
`floor(10qy)=10a+e` by a multiple of `q`. Finally
`0 <= {qy}<1` gives `0 <= e <= 9`. `square`

## 5. Realization theorem

**Theorem 5.1 (fixed-seed realization, complete characterization).**
Let integers `a_{s,j}` be given for every `s in N_+` and `j in N_0`, with
`0 <= a_{s,j}<q_s`. The following are equivalent.

1. There exists `x in [0,1)` such that equation (1.1) holds for every
   `s in N_+` and `j in N_0`.
2. The array satisfies (PC), (BC), and (DS), with every quantifier exactly as
   stated in Sections 2 and 3.

When these conditions hold, the seed is unique and is

\[
  x=L_0=\sup_{s\in N_+}a_{s,0}/q_s.                              \tag{5.1}
\]

*Proof, necessity.* Assume item 1 and set

\[
  y_j=\{10^j x\}\in[0,1).
\]

Then `a_{s,j}=floor(q_s y_j)`.

For `t >= s`, apply Lemma 4.1 with `r=q_t/q_s`, `q=q_s`, and `y=y_j`.
This gives (PC).

For each `s,j`, the floor inequalities give

\[
  0\le y_j-a_{s,j}/q_s<1/q_s.                                   \tag{5.2}
\]

Because `q_s` tends to infinity, the lower endpoints `a_{s,j}/q_s` tend to
`y_j`. Hence their supremum is `L_j=y_j`. The strict upper floor inequality

\[
  y_j<(a_{s,j}+1)/q_s
\]

for every `s` is exactly (BC).

Finally `y_{j+1}={10y_j}`. Lemma 4.2 supplies

\[
  e_{s,j}=\lfloor10\{q_sy_j\}\rfloor\in\{0,\ldots,9\}
\]

and proves (DS) for every `s,j`.

*Proof, sufficiency.* Assume (PC), (BC), and (DS). Fix `j`. By (PC), the
half-open intervals `I_{s,j}` are nested. Their diameters are `1/q_s`, which
tend to zero. Define `y_j=L_j` by (3.1). Every lower endpoint is at most
`L_j`; (BC) says that `L_j` is strictly below every upper endpoint. Therefore

\[
  y_j\in I_{s,j}\quad\hbox{for every }s\in N_+.                  \tag{5.3}
\]

In particular `0 <= y_j < 1`, and (5.3) is equivalent to

\[
  a_{s,j}=\lfloor q_s y_j\rfloor                                \tag{5.4}
\]

for every `s`. The intersection contains no second point, because two points
in every `I_{s,j}` would have distance less than `1/q_s` for every `s`, hence
distance zero.

It remains to link the points for consecutive `j`. Divide the congruence in
(DS) by `q_s` and view both sides in the circle `R/Z`:

\[
  \left[\frac{a_{s,j+1}}{q_s}\right]
  =\left[10\frac{a_{s,j}}{q_s}+\frac{e_{s,j}}{q_s}\right].       \tag{5.5}
\]

Equation (5.4) gives

\[
  a_{s,j}/q_s\longrightarrow y_j,
  \qquad
  a_{s,j+1}/q_s\longrightarrow y_{j+1}.                         \tag{5.6}
\]

Moreover `0 <= e_{s,j}/q_s <= 9/q_s`, so the error tends to zero. Passing to
the limit in the circle, where multiplication by ten is continuous, gives

\[
  [y_{j+1}]=[10y_j]\quad\hbox{in }R/Z.                           \tag{5.7}
\]

Both `y_{j+1}` and `{10y_j}` are in `[0,1)` and represent the same circle
point. Therefore

\[
  y_{j+1}=\{10y_j\}.                                             \tag{5.8}
\]

This remains valid when `10y_j` is an integer: the representative is zero,
not one. Condition (BC) is what prevents the inverse limit from selecting the
excluded representative one.

Take `x=y_0`. Induction in (5.8) gives `y_j={10^j x}` for every `j`.
Substitution into (5.4) proves equation (1.1) for every `s,j`.

For uniqueness, any realizing seed belongs to every `I_{s,0}`; their
diameters tend to zero, so their intersection has at most one point. Thus it
must equal `L_0`. `square`

**Remark 5.2 (no digit-error coherence is missing).** The sufficiency proof
uses only `0 <= e_{s,j} <= 9`, hence `e_{s,j}/q_s -> 0`. It does not require
the selected digits to agree under projection. Once a seed has been
reconstructed, Lemma 4.2 supplies the canonical digit at each scale. Thus the
missing inverse-limit condition is the right-boundary condition (BC), not a
separate compatibility law for the digits.

## 6. Why projection and successors alone are insufficient

Define, for every `s in N_+` and `j in N_0`,

\[
  a_{s,j}=q_s-1.                                                  \tag{6.1}
\]

This array satisfies all range conditions. If `t >= s` and
`r=q_t/q_s`, then

\[
  P_{t\to s}(q_t-1)
  =\left\lfloor\frac{rq_s-1}{r}\right\rfloor
  =q_s-1,                                                         \tag{6.2}
\]

so (PC) holds. It also satisfies (DS) with `e_{s,j}=9`, because

\[
  10(q_s-1)+9=10q_s-1\equiv q_s-1\pmod {q_s}.                   \tag{6.3}
\]

However,

\[
  L_j=\sup_s\frac{q_s-1}{q_s}=1
  =\frac{a_{s,j}+1}{q_s}                                         \tag{6.4}
\]

for every `s,j`, so every required strict inequality in (BC) fails. The
nested cells are `[1-1/q_s,1)` and have empty intersection in `[0,1)`.

If a realizing `x` existed, already at `j=0` it would satisfy
`x >= 1-1/q_s` for every `s`, hence `x >= 1`, contradicting `x<1`.
Therefore (PC) and (DS), even together with all label bounds and
`q_s -> infinity`, do not characterize fixed-seed arrays. The explicit
missing condition is (BC).

## 7. Equivalent boundary formulations

Under (PC), the following are equivalent for each fixed `j`:

1. (BC) holds for that `j` at every `s`.
2. The intersection `intersection_{s>=1} I_{s,j}` is nonempty.
3. That intersection consists of the single point `L_j`.

Indeed, (BC) puts `L_j` in every cell, while nonemptiness and shrinking
diameters give a unique point `y`; inequality (5.2) then forces `L_j=y` and
the half-open cell condition forces the strict inequalities in (BC). This
equivalence is useful for intuition, but the explicit supremum inequalities
are the auditable form used in Theorem 5.1.

## 8. T28 cross-scale incompatibility

The kernel-checked T28 family is indexed by `n >= 1` and has

\[
  M_n=10^n,\qquad D_n=3^n,\qquad
  q_n=9D_nM_n=9\cdot30^n,\qquad
  x_n=\frac1{9D_n}.                                               \tag{8.1}
\]

Thus its moduli are exactly the chain used above, but its seed depends on
`n`. For every sampled `0 <= j < M_n`, define the ordinary integer label by

\[
  a^{T28}_{n,j}=(\operatorname{orbitLabel}(n,j)).\operatorname{val}
  \in\{0,\ldots,q_n-1\}.                                         \tag{8.2}
\]

The kernel-checked theorem
`DecimalFactorComplexity.ScaleDependentDecimalOrbit.orbitLabel_eq_natCast`
then gives

\[
  a^{T28}_{n,j}\equiv M_n10^j\pmod {q_n}.                        \tag{8.3}
\]

At `j=0`, because `0 < M_n < q_n`, the standard integer representative is

\[
  a^{T28}_{n,0}=M_n=10^n.                                        \tag{8.4}
\]

Consecutive moduli satisfy

\[
  \frac{q_{n+1}}{q_n}
  =\frac{9\cdot30^{n+1}}{9\cdot30^n}=30.                        \tag{8.5}
\]

Therefore the fine label at time zero projects to

\[
\begin{aligned}
  P_{n+1\to n}(a^{T28}_{n+1,0})
    &=\left\lfloor\frac{10^{n+1}}{30}\right\rfloor\\
    &=\left\lfloor\frac{10^n}{3}\right\rfloor\\
    &<10^n
     =a^{T28}_{n,0}.                                              \tag{8.6}
\end{aligned}
\]

The strict inequality holds for every `n >= 1` because `10^n/3 < 10^n`.
For the smallest scale, the calculation is fully numerical:

\[
  q_1=270,\quad a^{T28}_{1,0}=10,\quad
  q_2=8100,\quad a^{T28}_{2,0}=100,\quad
  P_{2\to1}(100)=\lfloor100/30\rfloor=3\ne10.                   \tag{8.7}
\]

The index `j=0` lies in both finite T28 samples, so no extension beyond T28's
sample ranges is being assumed. Equation (8.6) is a direct failure of (PC).
Consequently the moving-seed T28 labels cannot be restrictions of one
cross-scale floor-quantized orbit. This conclusion is only about coherence of
that explicit rational family. It has no pi-specific or entropy consequence.

## 9. Audit checklist and conclusion

The realization interface consists of exactly:

1. the explicit chain `q_s=9*30^s`, with quotient `30^(t-s)`;
2. floor-cell projection (2.1), not modular reduction;
3. all-pairs projection compatibility (PC);
4. the strict, all-scale boundary inequalities (BC);
5. the all-time digit-successor congruences (DS);
6. the limit `q_s -> infinity`, used both for uniqueness and to make
   `e_{s,j}/q_s -> 0`;
7. reconstruction `x=L_0` and `y_j=L_j`.

Projection and successor data alone admit the explicit non-realizable array
in Section 6. Adding (BC) gives the if-and-only-if Theorem 5.1. T28 fails even
the projection part at the common index `j=0`, by the reproducible calculation
(8.6). All results in this note remain at `proof sketch` level.
