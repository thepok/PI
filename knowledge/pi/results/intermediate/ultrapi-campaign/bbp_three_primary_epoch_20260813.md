# BBP three-primary denominator epochs and synchronized residual orbit

Audit date: **2026-08-13 UTC**

Target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt)

Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.

Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

Parent report:
[bbp_odd_cofactor_short_orbit_experiment_20260813.md](bbp_odd_cofactor_short_orbit_experiment_20260813.md),
SHA-256
`c648520d7c118ed63326afffce407a05ff2b05ca69efae36caeb20d1a06851c3`.

## Outcome and claim status

No proof that every finite decimal word occurs in pi was obtained. V1 remains
a `conjecture`.

This branch gives an all-depth exact description, with status `proof sketch`,
of the 3-primary denominator and its leading unit for the BBP partial sum

\[
 B_M=\sum_{k=0}^{M}\frac{a(k)}{16^k}.
\]

The apparent denominator drops at \(M=5,50,455,4100,\ldots\) are not noise.
They are forced cancellations at the third pole of every even 3-adic epoch.
The exponent drops by exactly one, then rises by two when the next odd epoch
begins. The complete formula is in Section 2.

There is also a precise answer to the residual-row question. After the fixed
factor

\[
                         v_3(10^n-16)=1
\]

is removed, the isolated 3-primary coordinate has exact period
\(3^{E_M-2}\) when \(E_M\ge2\). On infinitely many proportional BBP rows it
traverses its entire uniformly spaced coset. Thus this coordinate alone
approximates every circle target increasingly well.

This does **not** prove a return of the complete BBP phase. Every other CRT
coordinate moves with the same exponent \(n\); no independence or joint
discrepancy estimate is known. The result exposes a synchronized resonance,
not a V1 breakthrough.

The companion bounded replay through \(M=5000\) has status `experiment`. It
uses exact rational and integer arithmetic and is not promoted into a proof.

## 1. Normalized question and quantifiers

Use the exact coefficient

\[
 a(k)=\frac{120k^2+151k+47}
 {(2k+1)(4k+3)(8k+1)(8k+5)}
 =\frac4{8k+1}-\frac1{2(2k+1)}
  -\frac1{8k+5}-\frac1{2(4k+3)}.                 \tag{1}
\]

Write the reduced rational as

\[
 B_M=\frac{P_M}{2^{K_M}3^{E_M}S_M},
 \qquad (P_M,6S_M)=1,\quad (S_M,3)=1.             \tag{2}
\]

Here “3-primary denominator” means the exponent \(E_M=-v_3(B_M)\) in
the **reduced** denominator, not the largest power of 3 appearing in an
unreduced summand. Define its leading unit by

\[
 u_M\equiv 3^{E_M}B_M\pmod3,\qquad u_M\in\{1,2\}. \tag{3}
\]

The following distinctions are essential.

1. The denominator formula below is for every integer \(M\ge0\), not only
   for the computed range.
2. The orbit statement is for the isolated 3-primary additive CRT
   coordinate. “It hits a target” does not mean that the full rational phase
   hits the same target.
3. The row window is exactly
   \(M\le n\le U_M:=\lfloor\log_{10}(16^M)\rfloor\).
4. The finite replay is an `experiment`; the symbolic argument is a
   `proof sketch` and has not been formalized in Lean.

## 2. Exact epoch formula

For odd \(e\ge1\), set

\[
 \delta_e=\frac{3^e-3}{4},\qquad
 \alpha_{e+1}=\frac{3^{e+1}-1}{8}.                \tag{4}
\]

For even \(e\ge2\), set

\[
 \alpha_e=\frac{3^e-1}{8},\qquad
 \beta_e=\frac{3^e-1}{2},\qquad
 \gamma_e=\frac{5(3^e-1)}8,\qquad
 \delta_{e+1}=\frac{3(3^e-1)}4.                  \tag{5}
\]

All displayed thresholds are integers:
\(3^e\equiv3\pmod4\) for odd \(e\), while
\(3^e\equiv1\pmod8\) for even \(e\). The half-open intervals in
(4)--(5) partition all \(M\ge0\).

### `proof sketch`

For every \(M\ge0\), the exact reduced-denominator exponent and leading unit
are

\[
\begin{array}{c|c|c}
\text{depth interval}&E_M&u_M\\ \hline
\delta_e\le M<\alpha_{e+1},\ e\text{ odd}&e&1\\
\alpha_e\le M<\beta_e,\ e\text{ even}&e&1\\
\beta_e\le M<\gamma_e,\ e\text{ even}&e&2\\
\gamma_e\le M<\delta_{e+1},\ e\text{ even}&e-1&2.
\end{array}                                                     \tag{6}
\]

The beginning of (6) is

\[
\begin{array}{c|rrrrrrrrrrrrrrrrr}
M&0&1&4&5&6&10&40&50&60&91&364&455&546&820&3280&4100&4920\\
\hline
E_M&1&2&2&1&3&4&4&3&5&6&6&5&7&8&8&7&9\\
u_M&1&1&2&2&1&1&2&2&1&1&2&2&1&1&2&2&1.
\end{array}                                                     \tag{7}
\]

Rows in (7) mark state changes; values between two successive entries persist
as specified by (6).

## 3. Why the three-pole cancellation drops exactly one level

For the four partial fractions in (1), record the pole form and coefficient

\[
\begin{array}{c|c}
\ell_i(k)&c_i\\ \hline
8k+1&4\\
2k+1&-1/2\\
8k+5&-1\\
4k+3&-1/2.
\end{array}                                                     \tag{8}
\]

Suppose \(\ell_i(k)=q3^t\) with \(3\nmid q\). After multiplication by
\(3^t\), its leading residue modulo 3 is

\[
                   c_iq^{-1}16^{-k}\equiv c_iq^{-1}\pmod3.    \tag{9}
\]

The relevant coefficient residues are \(1,1,2,1\), respectively.

For completeness, the first index at which each form has **exactly** height
\(t\) is obtained by solving
\(\ell_i(k)=q3^t\), choosing the least positive admissible \(q\) with
\(3\nmid q\):

\[
\begin{array}{c|c|c}
\ell_i& t\text{ odd}&t\text{ even}\\ \hline
8k+1&(11\cdot3^t-1)/8&(3^t-1)/8\\
2k+1&(3^t-1)/2&(3^t-1)/2\\
8k+5&(7\cdot3^t-5)/8&(5\cdot3^t-5)/8\\
4k+3&(3^t-3)/4&(7\cdot3^t-3)/4.
\end{array}                                                     \tag{8a}
\]

For example, when \(t\) is odd the congruence for \(8k+1\) first permits
\(q=3\), but that gives height \(t+1\); the first \(q\) prime to 3 is
\(11\). The other entries follow from the residue conditions modulo 8, 2,
8, and 4.

Table (8a) also proves the interval partition rather than merely suggesting
it. For odd \(e\), the \(4k+3\) pole at \(\delta_e\) occurs no later than
every other exact height-\(e\) pole, while the next record pole is
\(8\alpha_{e+1}+1=3^{e+1}\). For even \(e\), put
\(A=(3^e-1)/8\). Before the next record, the only height-\(e\) poles arrive
at

\[
                         A,\quad4A,\quad5A,                   \tag{8b}
\]

and the next record is
\[
                  6A=\delta_{e+1},\qquad4(6A)+3=3^{e+1}.     \tag{8c}
\]

Here is an explicit endpoint check. Put \(P=3^e\). On an odd half-open
interval, \(M\le\alpha_{e+1}-1\), so the four pole forms are respectively
less than \(3P,P,3P,2P\). Their required \(q\)-classes leave only \(q=1\)
in the fourth form. On an even half-open interval,
\(M\le\delta_{e+1}-1\), the four forms are respectively less than
\(6P,2P,6P,3P\). Their required \(q\)-classes leave exactly
\(q=1,1,5\) in the first three forms and none in the fourth. Thus no
unlisted height-\(e\) pole, nor any higher pole, can occur before the stated
right endpoint. Starting with
\(\delta_1=0,\alpha_2=1\), the end of every odd interval is the start of the
following even interval, and the end \(6A=\delta_{e+1}\) of every even
interval is the start of the following odd interval. Hence (4)--(5) are
disjoint and cover every \(M\ge0\).

For odd \(e\), throughout
\(\delta_e\le M<\alpha_{e+1}\), the unique pole of height \(e\) is

\[
                         4\delta_e+3=3^e.                     \tag{10}
\]

Its leading residue is \(-1/2\equiv1\pmod3\), proving the first row of
(6).

For even \(e\), height-\(e\) poles arrive at precisely

\[
\begin{array}{c|c|c|c}
M&\text{pole identity}&q&\text{leading residue mod }3\\ \hline
\alpha_e&8\alpha_e+1=3^e&1&1\\
\beta_e&2\beta_e+1=3^e&1&1\\
\gamma_e&8\gamma_e+5=5\cdot3^e&5&1.
\end{array}                                                     \tag{11}
\]

The successive sums \(1,2,0\pmod3\) prove the first two even rows of (6)
and show that a drop occurs at \(\gamma_e\). The next record pole is

\[
                 4\delta_{e+1}+3=3^{e+1}.                    \tag{12}
\]

It remains to prove that the drop at \(\gamma_e\) is exactly one level,
not more. The height-\(e\) cluster is

\[
 3^{-e}H_e,\qquad
 H_e=4\,16^{-\alpha_e}
      -\frac12\,16^{-\beta_e}
      -\frac15\,16^{-\gamma_e}.                              \tag{13}
\]

For every even \(e\ge2\),

\[
 \alpha_e\equiv\beta_e\equiv1\pmod3,
 \qquad\gamma_e\equiv2\pmod3.                               \tag{14}
\]

Since \(16\equiv7\pmod9\) has order 3, (14) gives

\[
 H_e\equiv4\cdot4-5\cdot4-2\cdot7
       =-18\equiv0\pmod9.                                    \tag{15}
\]

This congruence is in the localization \(\mathbb Z_{(3)}\), where every
displayed denominator is a unit: explicitly
\(1/2\equiv5\pmod9\) and \(1/5\equiv2\pmod9\). After scaling by
\(3^{e-1}\), the old height-\(e\) cluster is \(H_e/3\). Equation (15)
therefore places it in \(3\mathbb Z_{(3)}\), so its reduction modulo 3 is
indeed zero.

Put \(Q=3^{e-1}\). For every
\(\gamma_e\le M<\delta_{e+1}\), direct endpoint inequalities and the four
linear congruences in (8) give the complete list of exact height-\(e-1\)
poles:

\[
\begin{array}{c|c|c}
\ell_i&\{q: \ell_i(k)=qQ,\ 3\nmid q\}&
 \text{total residue from (9)}\\ \hline
8k+1&\{11\}&2\\
2k+1&\{1\}&1\\
8k+5&\{7\}&2\\
4k+3&\{1,5\}&0.
\end{array}                                                     \tag{16}
\]

For example, with

\[
 \gamma_e=\frac{15Q-5}{8},\qquad
 \delta_{e+1}=\frac{9Q-3}{4},                                \tag{17}
\]

at the lower endpoint the four normalized pole maxima are respectively
\[
 15-\frac4Q,\qquad\frac{15-1/Q}{4},\qquad15,\qquad
 \frac{15+1/Q}{2},
\]
and before the upper endpoint they are strictly below
\(18,9/2,18,9\). The first pole requires
\(q\equiv3\pmod8\), leaving only \(q=11\) after excluding multiples of
3. The other three forms require \(q\) odd,
\(q\equiv7\pmod8\), and \(q\equiv1\pmod4\), respectively. Filtering both
endpoint bounds gives exactly the four sets in (16), all already present at
\(M=\gamma_e\). Their total residue is
\(2+1+2+0\equiv2\pmod3\). Together with (15), this proves
\(E_M=e-1\) and \(u_M=2\) on the drop interval.

Solving the same four linear congruences for the first admissible pole gives
the ordered thresholds (4)--(5) and shows that no unlisted pole of equal or
greater height occurs between them. This completes the `proof sketch` of
(6).

## 4. Exact residual 3-primary phase

Let

\[
 \beta_M\equiv P_M(2^{K_M}S_M)^{-1}\pmod {3^{E_M}}.           \tag{18}
\]

Then \(\beta_M\equiv u_M\pmod3\), and the additive CRT decomposition of
\(B_M\pmod1\) has 3-primary coordinate
\(\beta_M/3^{E_M}\).

For \(n\ge1\), put

\[
                     g_n=\frac{10^n-16}{3}.                  \tag{19}
\]

The elementary congruence \(10^n\equiv1\pmod9\) gives
\(g_n\equiv1\pmod3\), equivalently

\[
                         v_3(10^n-16)=1.                     \tag{20}
\]

Therefore the 3-primary component of the actual BBP row phase
\((10^n-16)B_M\) reduces from denominator \(3^{E_M}\) to

\[
 \boxed{
   \frac{\delta_{M,n}}{3^{E_M-1}},\qquad
   \delta_{M,n}\equiv\beta_Mg_n\pmod {3^{E_M-1}}.}           \tag{21}
\]

When \(E_M=1\), this coordinate is integral and disappears. When
\(E_M\ge2\), its numerator always lies in the fixed rowwise coset

\[
                       \delta_{M,n}\equiv u_M\pmod3.         \tag{22}
\]

### Exact orbit

### `proof sketch`

LTE gives, for every \(h\ge1\),

\[
                    v_3(10^h-1)=2+v_3(h).                    \tag{23}
\]

Consequently, for \(E\ge2\), the order of 10 modulo \(3^E\) is

\[
                            T_E=3^{E-2}.                      \tag{24}
\]

Indeed,

\[
 g_n\equiv g_m\pmod {3^{E-1}}
 \iff 10^n\equiv10^m\pmod {3^E}
 \iff n\equiv m\pmod {T_E}.                                 \tag{25}
\]

There are \(T_E\) residues modulo \(3^{E-1}\) congruent to 1 modulo 3.
Equations (19), (22), and (25) therefore show that one period of \(g_n\)
runs bijectively through the former coset, while one period of
\(\delta_{M,n}\) runs bijectively through

\[
       \{u_M+3j:0\le j<T_E\}\pmod {3^{E-1}}.                 \tag{26}
\]

As circle points, (26) is a translate of the uniform grid with \(T_E\)
points and spacing \(1/T_E\).

## 5. What the proportional row does and does not hit

The number of exponents in the exact BBP row is

\[
\begin{aligned}
 L_M
 &=U_M-M+1\\
 &=\left\lfloor\log_{10}\left((8/5)^M\right)\right\rfloor+1.
                                                                  \tag{27}
\end{aligned}
\]

For \(E_M\ge2\), the isolated 3-primary coordinate covers its full grid
if and only if

\[
                            L_M\ge T_{E_M}.                    \tag{28}
\]

This is exact: a shorter window cannot repeat or cover the orbit by (25),
whereas any \(T_{E_M}\) consecutive exponents form a complete period.

There are infinitely many full-grid rows. For even \(e\ge2\), take the
last pre-drop depth \(M=\gamma_e-1\). With \(T=3^{e-2}\),

\[
 M=\frac{45T-13}{8}\ge5(T-1).                                \tag{29}
\]

Since

\[
                    (8/5)^5=32768/3125>10,                    \tag{30}
\]

(27)--(30) imply \(L_M\ge T\). Moreover, for every even \(e\ge4\),
every depth in the drop interval has \(E_M=e-1\), period
\(T=3^{e-3}\), and

\[
 M\ge\gamma_e=\frac{135T-5}{8}>5(T-1).                       \tag{31}
\]

So every such drop row covers its complete isolated 3-primary grid.

By contrast, no nontrivial odd epoch covers a complete grid. For odd
\(e\ge5\), put \(T=3^{e-2}\). Then

\[
 M\le\alpha_{e+1}-1=\frac{27T-9}{8}\le4(T-1),                \tag{32}
\]

and \((8/5)^4<10\) forces \(L_M<T\). The small odd epoch \(e=3\),
\(6\le M\le9\), has \(L_M=2<T=3\) by direct integer comparison; \(e=1\)
has only the trivial denominator after (20).

On a full-grid row, the isolated coordinate comes within \(1/(2T)\) of
every prescribed circle target. Since \(T\to\infty\) along the even epochs,
this is genuine one-coordinate target approximation.

It is nevertheless another resonance for the complete problem. If the
remaining CRT coordinates are denoted by \(\chi_{M,n}\), the phase to control
is

\[
       \frac{\delta_{M,n}}{3^{E_M-1}}+\chi_{M,n}\pmod1,       \tag{33}
\]

not its first summand. Both summands are selected by the same short exponent
window. A complete grid in the first coordinate gives no bound on (33)
without a joint estimate: a synchronized second coordinate could, in
principle, cancel the grid motion exactly. Changing \(M\) changes \(u_M\),
\(\beta_M\), the dyadic coordinate, and every other odd-primary coordinate
together. Neither the epoch variation nor the proportional window supplies
the missing independence.

A tempting fixed-dimensional upgrade is also not supplied by the currently
pinned Bourgain--Chang theorem. If \(Q\) is a product of finitely many good
high primes and \(\xi/Q\) is their primitive additive coordinate, the
standard power-generator expression for the joint phase uses the unreduced
modulus

\[
                         q=3^{E_M}Q.                         \tag{34}
\]

Its combined numerator is primitive: modulo 3 only the 3-primary numerator
survives, while modulo each \(p\mid Q\) only
\(\xi3^{E_M}\) survives. This observation corrects a possible off-by-one:
working instead at the reduced phase denominator \(3^{E_M-1}Q\) replaces
\(10^n\) by \(g_n=(10^n-16)/3\), which is not a fixed coefficient times
\(10^n\) modulo \(3^{E_M-1}\).

However, Bourgain--Chang define “few prime factors” for
\(q=\prod p_\alpha^{\nu_\alpha}\) by a uniform bound on
\(\sum_\alpha\nu_\alpha\). The exponent \(E_M\) in (34) is unbounded.
Their incomplete-sum Corollary 4.5 also requires
\(\operatorname{ord}_p(10)>q^\delta\) for every base prime \(p\mid q\),
whereas \(\operatorname{ord}_3(10)=1\). Thus their fixed-high-prime
projection theorem cannot simply absorb this 3-primary coordinate. This is
a source-specific applicability obstruction, not a proof that no future
joint estimate can do so.

Thus the 3-primary branch is now explicit, but it does not close the
short-orbit problem isolated in the parent report.

## 6. Exact bounded replay

The companion checker is
[bbp_three_primary_epoch_20260813_check.py](bbp_three_primary_epoch_20260813_check.py),
SHA-256
`4cb663d1d484c750ad99d2120d13143c24297ab4f81860a9f1584d5018ea2fa1`.

Its default run constructs every \(B_M\) as a reduced `Fraction` through
\(M=5000\). It checks (6) at every depth, verifies the complete lower-pole
list (16) at every fully visible even epoch, enumerates each residual orbit,
and checks proportional-row coverage with exact integer logarithms. Its
output was:

```text
claim_status=experiment
source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
parent_report_sha256=c648520d7c118ed63326afffce407a05ff2b05ca69efae36caeb20d1a06851c3
max_depth=5000
partial_fraction_identity_checks=5001
exact_fraction_epoch_checks=5001
symbolic_epoch_structure_checks=40
even_boundary_cluster_checks=4
primary_orbit_checks=8
direct_residual_phase_checks=49
exact_row_window_checks=5001
full_grid_rows=1533
nontrivial_odd_epoch_rows=390
nontrivial_odd_full_grid_rows=0
certified_even_drop_rows=921
max_three_primary_exponent=9
observed_state_transitions=0:E1/u1/odd,1:E2/u1/even-first,4:E2/u2/even-second,5:E1/u2/even-drop,6:E3/u1/odd,10:E4/u1/even-first,40:E4/u2/even-second,50:E3/u2/even-drop,60:E5/u1/odd,91:E6/u1/even-first,364:E6/u2/even-second,455:E5/u2/even-drop,546:E7/u1/odd,820:E8/u1/even-first,3280:E8/u2/even-second,4100:E7/u2/even-drop,4920:E9/u1/odd
v1_status=not_proved
status=PASS
```

All statements derived only from this bounded run have status `experiment`.
The replay neither evaluates decimal digits of pi nor proves a full-phase
return.

## 7. Literature and mathlib audit

### `literature-checked`

Search date: **2026-08-13 UTC**.

The search used the exact strings `"BBP" 3-adic denominator`,
`"120k^2+151k+47" 3-adic`, and weighted/harmonic partial-sum variants.
It found no source directly stating (6), (15), or the four-pole epoch
calculation. This is a bounded search report, not a novelty claim.

- Bailey--Borwein--Plouffe,
  [On the Rapid Computation of Various Polylogarithmic Constants](https://doi.org/10.1090/S0025-5718-97-00856-9),
  is the primary source for the base-16 BBP formula, but does not provide the
  present reduced-partial-sum valuation theorem.
- Sanna,
  [On the p-adic valuation of harmonic numbers](https://doi.org/10.1016/j.jnt.2016.02.020),
  studies \(p\)-adic valuations of ordinary harmonic numbers rather than this
  weighted four-pole BBP sum.
- Carofiglio--De Filpo--Gambini,
  [On the \(p\)-adic valuation of harmonic sums](https://arxiv.org/abs/2303.15010),
  gives further harmonic-sum context, again not the exact coefficient in
  (1).
- Bourgain--Chang,
  [Exponential Sum Estimates over Subgroups and Almost Subgroups of
  \(\mathbb Z_q^*\)](https://doi.org/10.1007/s00039-006-0558-7),
  Corollaries 4.2 and 4.5 were checked for the proposed joint-coordinate
  upgrade. Section 4's bounded-multiplicity definition and the
  \(\operatorname{ord}_p\) condition give the obstruction following (34).
  The locally pinned
  [PDF](../theory/pi-lacunary-near-return-sparsity/library/t124/bourgain-chang-2006.pdf)
  has SHA-256
  `a4c130e401ff03a5b91fbd20339f06021f26bf871ca2bb375f2ce25e3ee5d1d7`.

The local mathlib search found the needed generic vocabulary but no direct
formalization of (6):

- `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean` defines rational
  \(p\)-adic valuation;
- `Mathlib/NumberTheory/Multiplicity.lean` contains
  `Int.emultiplicity_pow_sub_pow`, an LTE theorem suitable for (23);
- `Mathlib/NumberTheory/Harmonic/Int.lean` proves
  `padicValRat_two_harmonic` for ordinary harmonic numbers at 2, not this
  BBP sum at 3.

No formal file was changed, so there is no `machine-checked` claim and no
axiom-audit entry to register.

## 8. Reproduction

From the repository root:

```bash
python work/ultrapi-resume/bbp_three_primary_epoch_20260813_check.py
```

No `ultrapi.md` or verified-track file was edited by this branch.

## 9. Coordination record

This branch registered area watch `ultrapi-three-primary-20260813` on
`local:pi-digits` for agent `codex-ultrapi-three-primary`. Its initial and
final polls were both empty at cursor and delivered sequence 57,210, so
there was no event to acknowledge. Observation events would have been
treated only as coordination signals, not as mathematical evidence.
