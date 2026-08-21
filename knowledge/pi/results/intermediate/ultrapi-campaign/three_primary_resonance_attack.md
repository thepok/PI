# Nested three-primary resonance and threshold aliases

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's immutable local source contains no external source URL,
so none is invented here.  
Route: [T52's exact three-primary denominator](../../TheoryLib/PiQuantitativeBlockHitting/T52T52MachinSeedThreePrimaryPersistence.lean), equations (23)--(28) of
[`actual_shift_resonance_attack.md`](actual_shift_resonance_attack.md), and
T38/T46's exact forced Machin recurrence.

## Outcome and claim status

No proof that every finite decimal word occurs in \(\pi\) was obtained. The
canonical target remains a `conjecture`.

T52 removes one genuine defect from the earlier cross-index Fourier attempt:
if the complementary modulus is the **complete** three-primary denominator,
then

\[
 D_j=3^{a_j-1},\qquad
 3^{a_j}\le 12j+3<3^{a_j+1},                       \tag{1}
\]

and \(D_j\mid D_{j+1}\), with quotient either \(1\) or \(3\). The resonant
frequency family therefore closes exactly across seed indices:

\[
 \boxed{P_{j+1}(\ell)=P_j(10\tau_j\ell)
             e(\ell D_{j+1}\Delta_j),\qquad
        \tau_j={D_{j+1}\over D_j}\in\{1,3\}.}     \tag{2}
\]

Here \(P_j(\ell)=e(\ell D_jx_j)\), \(x_j\) is the actual reduced Machin
phase, and \(\Delta_j\) is T38's exact rational forcing.

This closure does **not** yield contraction. At a tripling threshold, the
new grid is the disjoint union of three translates of the inherited grid.
Fourier cancellation between those three aliases removes two residue classes
of frequencies from the **full** new grid, but the actual orbit remains in
one inherited alias. That single alias retains all three frequency classes.
Between thresholds, multiplication by ten merely permutes the grid, with
short order \(D_j/9\) and nine invariant residue classes once \(D_j\ge9\).

Sections 2--7 give exact elementary derivations, retained as a `proof sketch`
because they have not been formalized in Lean. Section 8 gives a structural
`proof sketch` separator: the same nested \(D_j\), positive rational
coboundary, T46-size geometric telescope, and closed frequency recurrence
can coexist with an orbit shadowing \(0.1111\ldots\) and avoiding digit zero
at every natural-length pulse. It does not preserve the actual Machin forcing
or actual non-three-primary residues, so it does not refute an
actual-numerator theorem. It does prove that nesting plus the generic
T38/T46 bounds alone cannot supply ASR.

The exact finite checker is an `experiment`; finite evidence is not used as
proof.

## 1. Normalized target and exact split

The canonical V1 statement is

\[
 \forall m\in\mathbb N\;\forall w\in\{0,\ldots,9\}^m\;
 \exists n\in\mathbb N:\quad
 (d_n(\pi),\ldots,d_{n+m-1}(\pi))=w.               \tag{3}
\]

Digits are after the decimal point, leading zeroes in \(w\) are allowed,
and \(m=0\) is vacuous. This is contiguous finite occurrence, not
subsequence occurrence and not normality.

For \(j\ge1\), put

\[
 y_j=10^jM_{3j},\qquad x_j=\{y_j\}={b_j\over Q_j},
 \qquad 0\le b_j<Q_j,                              \tag{4}
\]

where \(b_j/Q_j\) is reduced. T52 proves the exact valuation and reduced
denominator multiplicity corresponding to (1). Use the coprime split

\[
 Q_j=F_jD_j,\qquad (F_j,D_j)=1,
 \qquad b_j=F_jc_j+r_j,\qquad 0\le r_j<F_j.       \tag{5}
\]

Then

\[
 x_j={c_j\over D_j}+{r_j\over F_jD_j},\qquad
 \phi_j:={r_j\over F_j}=\{D_jx_j\}.                \tag{6}
\]

Thus the exact shifted grid and its actual member are

\[
 G_j=x_j+{1\over D_j}\mathbb Z/\mathbb Z
    ={r_j\over F_jD_j}+{1\over D_j}\mathbb Z/\mathbb Z,
 \qquad x_j\in G_j.                                \tag{7}
\]

The resonant phase from the shifted-grid Poisson formula is precisely

\[
 P_j(\ell):=e(\ell\phi_j)=e(\ell D_jx_j).          \tag{8}
\]

## 2. Exact tripling thresholds

For \(a\ge2\), the first index in the \(a\)-th band is

\[
 J_a:=\min\{j\ge1:3^a\le12j+3\}
 =\begin{cases}
 (3^a-3)/12,&a\text{ odd},\\
 (3^a+3)/12,&a\text{ even}.
 \end{cases}                                       \tag{9}
\]

This uses \(3^a\equiv3\pmod {12}\) for odd \(a\) and
\(3^a\equiv9\pmod {12}\) for even \(a\). Consequently

\[
 D_j=3^{a-1}\quad(J_a\le j<J_{a+1}),               \tag{10}
\]

and the plateau length is

\[
 J_{a+1}-J_a=
 \begin{cases}
 (D_j+1)/2,&a\text{ odd},\\
 (D_j-1)/2,&a\text{ even}.
 \end{cases}                                       \tag{11}
\]

In particular \(a_{j+1}-a_j\in\{0,1\}\), giving
\(\tau_j=D_{j+1}/D_j\in\{1,3\}\). The first checked transitions are

\[
 3\to9\ (j=1),\quad9\to27\ (j=6),\quad
 27\to81\ (j=19),\quad81\to243\ (j=60).          \tag{12}
\]

There is at most one tripling during a T46 pulse of \(2J\) steps, since

\[
 12(3J)+3=36J+3<3(12J+3).                          \tag{13}
\]

The translation permutation inside one plateau is also unusually far from a
generic mixer. For \(D=3^{a-1}\ge9\), the lifting-the-exponent identity

\[
 v_3(10^n-1)=2+v_3(n)                              \tag{14}
\]

gives

\[
 \operatorname{ord}_{D}(10)=3^{a-3}=D/9.           \tag{15}
\]

Moreover \(10t\equiv t\pmod9\), so the permutation preserves all nine
classes \(t\bmod9\). The plateau has about \(4.5\) such periods, but the
base phase \(x_j\) changes throughout; periodicity of the translation
coordinate is not periodicity of the actual digit output.

## 3. The closed cross-index frequency map

T38/T46 give the exact unwrapped and circle recurrences

\[
 y_{j+1}=10y_j+\Delta_j,\qquad
 x_{j+1}=\{10x_j+\Delta_j\}.                       \tag{16}
\]

Multiplying the second identity by \(D_{j+1}=\tau_jD_j\) and taking a
fractional part gives

\[
 \boxed{\phi_{j+1}
   =\{10\tau_j\phi_j+D_{j+1}\Delta_j\}.}          \tag{17}
\]

Applying \(e(\ell\cdot)\) yields (2). Thus ordinary steps send
\(\ell\mapsto10\ell\), while tripling steps send
\(\ell\mapsto30\ell\). Unlike the general complementary factor in the
earlier report, this is an integer frequency at every step.

Iteration is equally exact. Write

\[
 R_{J,s}=\sum_{u=0}^{s-1}10^{s-1-u}\Delta_{J+u}.
\]

Then T46 gives

\[
 y_{J+s}=10^sy_J+R_{J,s},\qquad
 0\le R_{J,s}<10^s\rho^J,\qquad
 \rho={10\over625^3}.                              \tag{18}
\]

Since a \(2J\)-pulse crosses at most one threshold, put
\(\sigma_{J,s}=D_{J+s}/D_J\in\{1,3\}\). The iterated frequency identity is

\[
 \boxed{P_{J+s}(\ell)=
   P_J(10^s\sigma_{J,s}\ell)
   e(\ell D_{J+s}R_{J,s}).}                        \tag{19}
\]

This is a real improvement in exact bookkeeping. It is not cancellation:
the large frequency in (19) is a power-of-ten digital alias of the original
actual phase.

## 4. Exact grid map and the threshold aliases

For \(t\in\mathbb Z/D_j\mathbb Z\), (16) gives

\[
 \left\{10\left(x_j+{t\over D_j}\right)+\Delta_j\right\}
 =\left\{x_{j+1}+{10t\over D_j}\right\}.           \tag{20}
\]

If \(\tau_j=1\), multiplication by ten permutes
\(\mathbb Z/D_j\mathbb Z\), so (20) maps \(G_j\) bijectively onto
\(G_{j+1}\).

If \(\tau_j=3\), define

\[
 H_{j+1}^{(a)}=\left\{
 x_{j+1}+{u\over D_j}+{a\over3D_j}:0\le u<D_j
 \right\},\qquad a=0,1,2.                         \tag{21}
\]

Then

\[
 \boxed{G_{j+1}=H_{j+1}^{(0)}\sqcup H_{j+1}^{(1)}
                 \sqcup H_{j+1}^{(2)},\qquad
        T_j(G_j)=H_{j+1}^{(0)}.}                   \tag{22}
\]

In coordinates modulo \(D_{j+1}=3D_j\), the inherited points have coordinate
\(30t\), hence are exactly the coordinate class divisible by three. The
actual point corresponds to \(t=0\), so it always remains in the inherited
alias. The two new aliases are alternative coarse three-primary states, not
new possibilities for the already selected actual orbit.

This distinction is decisive. Let

\[
 \mathscr H_a(f)=\sum_{u=0}^{D_j-1}
 f\!\left(x_{j+1}+{u\over D_j}+{a\over3D_j}\right).
\]

For a boundary-safe Fourier expansion,

\[
 \boxed{\mathscr H_a(f)=D_j\sum_{k\in\mathbb Z}
 \widehat f(kD_j)P_j(10k)e(kD_j\Delta_j)e(ka/3).}  \tag{23}
\]

Summing the three aliases uses
\(\sum_{a=0}^2e(ka/3)=0\) unless \(3\mid k\), and gives

\[
 \sum_{a=0}^2\mathscr H_a(f)
 =3D_j\sum_{\ell\in\mathbb Z}
 \widehat f(3\ell D_j)P_j(30\ell)
 e(3\ell D_j\Delta_j).                            \tag{24}
\]

Equation (24) is exactly the \(D_{j+1}\)-grid Poisson formula and exactly the
frequency recurrence (2). But the actual inherited count is
\(\mathscr H_0(f)\), not the sum in (24). In (23) with \(a=0\), frequencies
\(k\equiv1,2\pmod3\) remain. Therefore the attractive cancellation at a
tripling threshold occurs only after adding two aliases which the actual
orbit does not follow.

For endpoints, one can replace (23)--(24) by the finite cyclic Fourier
identity from the companion report; the alias selection is then literal
finite subgroup orthogonality and has no convergence qualification.

## 5. Digit-automaton alignment, not contraction

For a fixed forbidden word \(w\), let \(A_a\) be its proper-prefix automaton
transition matrix for digit \(a\), with transitions completing \(w\)
deleted, and put

\[
 A=\sum_{a=0}^9A_a,qquad
 B_t(h)=\sum_{a=0}^9e(-ha/10^t)A_a.                \tag{25}
\]

The exact digital transform is

\[
 S_{w,n}(h)=v_0^{\mathsf T}
       \left(\prod_{t=1}^nB_t(h)\right)\mathbf1.
\]

At a power-of-ten alias,

\[
 B_t(10^vh)=
 \begin{cases}A,&t\le v,\\B_{t-v}(h),&t>v,
 \end{cases}
\]

and hence

\[
 S_{w,n}(10^vh)=v_0^{\mathsf T}A^v
       \left(\prod_{t=1}^{n-v}B_t(h)\right)\mathbf1.            \tag{26}
\]

The now-closed frequency map (2) lands **exactly** on these aliases. At an
ordinary step its multiplier is one factor of ten. At a threshold, the
factor three first selects one of the three grid aliases and the factor ten
again produces (26). The leading Perron component of \(A^v\) has size
\(\lambda_w^v\); no phase-free norm estimate makes the inherited alias
vanish.

There is also no pointwise occupancy recurrence. With natural depth
\(n_j=2j+m-1\), passing from \(j\) to \(j+1\) shifts the base point by one
decimal place while increasing the inspected string length by two. One old
leading position is lost and three new terminal positions enter. A grid
point which failed at the lost position can re-enter, so even monotonicity is
false. At a threshold, the full count additionally receives two new aliases.

The exact experiment found, already for one forbidden digit:

- at the ordinary step \(j=7\to8\), \(D=27\), the digit-2 avoidance count
  rises from \(6\) to \(7\);
- at \(j=21\to22\), \(D=81\), the digit-1 count rises from \(0\) to \(1\);
- at the threshold \(j=19\to20\), \(D=27\to81\), the digit-4 count rises
  from \(0\) to \(2\).

These are `experiment` witnesses. They falsify both monotonicity and the
tempting iid-style inequality

\[
 N_{j+1}\le\tau_j(9/10)^2N_j                      \tag{27}
\]

as universal pointwise recurrences. They do not falsify an eventual theorem
conditional on special actual-Machin phase information.

## 6. T46 forcing preserves the inherited alias

For an initial complementary choice \(t\bmod D_J\), define its exact forced
iterate by

\[
 z_{J+s}^{(t)}=
 \left\{10^s\left(x_J+{t\over D_J}\right)+R_{J,s}\right\}.
\]

Equations (18) and (20) give

\[
 \boxed{z_{J+s}^{(t)}=
   \left\{x_{J+s}+{10^st\over D_J}\right\}.}       \tag{28}
\]

Since \(D_J\mid D_{J+s}\), this is always a point of \(G_{J+s}\). If the
pulse crosses a tripling threshold, its coordinate modulo \(D_{J+s}\) is
\(3\cdot10^st\), so it remains in the inherited alias. No branching occurs
along an already selected trajectory.

T46's estimate in (18) is strong enough to transfer a finite itinerary when
the unforced point has a matching boundary margin. It supplies no such
margin for the actual point. The digit-filter operator on the finite set of
initial \(t\)'s is monotone as the forced itinerary is extended, but it has
no uniform strict contraction: all surviving states can emit an allowed
digit for arbitrarily many steps. Proving that the particular actual state
eventually dies under a missing-word assumption is again a statement about
the actual Archimedean phase.

## 7. Iteration returns to the fixed-\(\pi\) phase

Let \(s_j=10^j(\pi-M_{3j})\). T38 gives

\[
 x_j\equiv10^j\pi-s_j\pmod1,\qquad 0\le s_j<\rho^j.
\]

Consequently every closed phase in (19) is still

\[
 P_j(q10^v)=e(qD_j10^{j+v}\pi)e(-qD_j10^vs_j).     \tag{29}
\]

At the natural Fourier range the second factor is exponentially close to
one, exactly as in equations (26)--(27) of the companion report. The first
factor is the unresolved lacunary fixed-\(\pi\) phase. Nestedness has made its
index evolution integral; it has not estimated it.

Under a missing-word hypothesis, the actual point belongs to the inherited
alias at every valid shadow scale. Its occupancy is therefore at least one.
The zero mode is \(o(1)\). Thus the nonzero inherited-alias frequencies in
(23), including the two classes discarded by (24), must contribute
\(1-o(1)\). Ruling out that contribution is the actual-shift resonance
problem, not a consequence of (1), (18), or (26).

## 8. Structural all-1 separator (`proof sketch`)

The following explicit rational model shows sharply which input is still
missing. It preserves the exact three-primary schedule and the generic
T38/T46 geometry, but deliberately does **not** preserve the actual Machin
forcing or actual non-three-primary residues.

For \(j\ge2\), retain the same \(D_j\) from (1), and set

\[
 E_j=2\cdot10^{9j},\qquad
 \varepsilon_j={1\over D_jE_j},\qquad
 z_j={1\over9}-\varepsilon_j.                     \tag{30}
\]

Since \(9\mid D_j\),

\[
 z_j={D_jE_j/9-1\over D_jE_j}.                    \tag{31}
\]

This fraction is reduced. Every prime dividing \(E_j\) sees numerator
\(-1\), while the numerator is nonzero modulo three: for \(D_j=9\),
\(E_j\equiv2\pmod3\); for \(D_j\ge27\), it is \(-1\pmod3\). Hence the
complete three-primary denominator is exactly \(D_j\), and

\[
 \{D_jz_j\}=1-{1\over E_j}.                        \tag{32}
\]

Define the positive rational forcing

\[
 \eta_j=10\varepsilon_j-\varepsilon_{j+1}>0.       \tag{33}
\]

Because \(10/9\equiv1/9\pmod1\), it obeys the same circle recurrence form

\[
 z_{j+1}=\{10z_j+\eta_j\}.                         \tag{34}
\]

Its exact accumulated telescope is

\[
 \sum_{u=0}^{s-1}10^{s-1-u}\eta_{j+u}
 =10^s\varepsilon_j-\varepsilon_{j+s}.             \tag{35}
\]

Moreover \(10^{-9}<\rho\), so

\[
 0<10^s\varepsilon_j-\varepsilon_{j+s}
   <10^s\rho^j.                                    \tag{36}
\]

Thus (34)--(36) have the same positivity, geometric coboundary, and pulse
bound used in the generic T38/T46 transfer.

Nevertheless \(z_j\) begins with \(2j\) consecutive digit 1s. Indeed the
lower endpoint of that cylinder is

\[
 {1\over9}-{1\over9\cdot10^{2j}},
\]

and \(\varepsilon_j<1/(9\cdot10^{2j})\). Therefore the actual member
\(z_j\) of its \(D_j\)-grid avoids digit zero throughout the natural pulse,
so

\[
 N_j(0,2j)\ge1.                                    \tag{37}
\]

At the same time, \(D_j\le(12j+3)/3=4j+1\), and hence the zero mode satisfies

\[
 D_j(9/10)^{2j}\le(4j+1)(9/10)^{2j}\longrightarrow0.            \tag{38}
\]

The signed resonance is consequently at least \(1-o(1)\) at every scale in
this model. The phase (32) is an explicit digital major arc. All threshold
and power-of-ten frequency identities above still hold.

This separator rules out a proof of ASR based only on:

1. the exact nested schedule \(D_j=3^{a_j-1}\);
2. positivity and T46's geometric telescope bound;
3. closure of the frequency map under \(10\) and \(30\);
4. the forbidden-word automaton and its Perron entropy; or
5. the three-alias decomposition at thresholds.

It does **not** rule out using the exact values of \(\Delta_j\), the complete
actual phases \(r_j/F_j\), or a new arithmetic relation between those values
and the digit automaton. Those are precisely the data the separator changes.

## 9. Reproducible exact checks (`experiment`)

[`three_primary_resonance_check.py`](three_primary_resonance_check.py) uses
only `Fraction`, integer arithmetic, and the exact rational Machin seed
constructor from the companion experiment. It does not evaluate \(\pi\) or
read a digit table. SHA-256:
`5e1d861fe4a0e72e57f0a8e02d35bc07f69bcfc938cf77019c4ff701bdedff25`.

Commands:

```bash
python3 -m py_compile \
  work/ultrapi-resume/three_primary_resonance_check.py
python3 work/ultrapi-resume/three_primary_resonance_check.py --max-j 80
```

Retained output:

```text
claim_status=experiment
source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
j_range=1..80
exact_three_primary_valuation_checks=80
exact_phase_reciprocity_checks=80
threshold_formula_checks=5
order_of_ten_checks=4
two_j_pulse_threshold_checks=80
cross_index_transition_checks=79
cross_index_frequency_checks=1343
grid_image_point_checks=8337
threshold_alias_partition_checks=4
threshold_alias_rows=[(1, 3, 9), (6, 9, 27), (19, 27, 81), (60, 81, 243)]
t46_style_telescope_checks=2213
inherited_alternative_iterate_checks=6639
actual_seed_one_digit_avoidance_membership_checks=85800
naive_iid_contraction_violations=156
first_ordinary_positive_increases=[(7, '2', 6, 7), (7, '4', 4, 5), (7, '5', 5, 6), (7, '6', 4, 5), (9, '5', 4, 5)]
first_zero_resurrections=[(19, '0', 0, 1), (19, '3', 0, 1), (19, '4', 0, 2), (19, '5', 0, 1), (19, '6', 0, 2)]
artificial_denominator_checks=79
artificial_all_one_prefix_checks=79
artificial_subunit_zero_mode_survivals=64
artificial_recurrence_checks=78
artificial_telescope_checks=2131
all exact checks passed
```

The actual-seed rows verify T52's denominator value, phase reciprocity,
frequency closure, all finite threshold alias partitions, exact T46-style
telescopes, and inherited alternative iterates. The occupancy rows only
falsify the displayed naive recurrence. The artificial rows check finite
instances of (30)--(38); the general argument is the `proof sketch` above,
not an inference from those finite cases.

## 10. Sharp continuation target

The nesting breakthrough reduces the remaining theorem to a more precise
form, but does not prove it. A useful next result must control the **inherited
alias** with the actual phase. Sufficient possibilities include:

- a signed bound for (23) with \(a=0\), including the frequency classes
  \(k\equiv1,2\pmod3\), below the integer threshold;
- an arithmetic theorem excluding the actual phases \(r_j/F_j\) from the
  digital major arcs exemplified by (32); or
- a cross-index estimate using the exact actual forcing values
  \(\Delta_j\), not merely their positivity and T46 bound, to show that the
  actual inherited automaton state cannot survive a natural-length pulse.

A theorem for the full \(D_{j+1}\)-grid that obtains cancellation only by
summing all three threshold aliases is insufficient: the actual orbit uses
\(H^{(0)}\). Likewise, a contraction depending only on \(D_j\), automaton
entropy, or the geometric forcing bound is separated by (30)--(38).

## Bottom line

The complete three-primary component makes the cross-index resonant lattice
exactly nested and changes equation (28) from a nonclosing map into the
integer recurrence \(\ell\mapsto10\ell\) or \(30\ell\). This is meaningful,
inspectable progress. The same calculation also identifies why it does not
finish: a tripling creates three Fourier aliases, while the actual orbit
inherits only one; power-of-ten evolution aligns with the dangerous digital
aliases; and a fully explicit all-1 model satisfies every generic structural
input while maintaining resonance \(1-o(1)\). No unconditional cylinder hit,
`candidate resolution`, or `verified resolution` follows.
