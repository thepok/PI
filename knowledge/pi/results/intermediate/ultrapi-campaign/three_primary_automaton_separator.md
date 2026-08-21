# Three-primary quotient automaton and epoch separator

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

## Outcome and exact claim status

No complete proof that every finite decimal word occurs in pi was obtained.
The canonical target remains a `conjecture`.

The exact three-primary quotient dynamics can nevertheless be classified.
Starting with all \(D_J\) complementary quotient choices at an index \(J\),
the exact Machin recurrence creates **no new branches**.  During a constant
epoch it permutes the relative label by (t\mapsto10t); when the modulus
triples, it injects by (t\mapsto30t) into exactly one of the three new
cosets.  Coupling this label to the finite forbidden-word automaton gives an
exact finite, nonautonomous state machine.  Its survivor count is
nonincreasing, but neither the state map nor the epoch lengths supply a
strict contraction.

There are two rigorous `proof sketch` separators.

1. Keeping the exact schedule
   \(D_j=3^{\lfloor\log_3(12j+3)\rfloor-1}\), exact T53 carry equations,
   constant/tripling epochs, and a positive summable coboundary forcing of
   the same form as the Machin forcing, there is an explicit infinite
   constant-digit orbit.  It avoids any prescribed nonempty word after
   selecting a constant digit whose repeated block is different from it.
2. More strongly, on every sufficiently late complete epoch one can use the
   **actual numerical Machin forcing** and construct a rational state whose
   reduced denominator has the exact T52 three-primary part at every step,
   including the following tripling step, while its output digit is constant
   throughout the epoch.  This state deliberately does not retain the actual
   non-three fine residue.

Thus an extinction theorem based only on T52, T53, the exact forcing values,
and the constant/tripling schedule is false if it is uniform over the
non-three fine state.  The remaining possible source of contraction is the
special correlation between the **actual** Machin fine residues and the one
actual coarse quotient.  The separators do not address that correlation and
are not counterexamples involving pi.

The statements already proved in
[`T52T52MachinSeedThreePrimaryPersistence.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T52T52MachinSeedThreePrimaryPersistence.lean)
(SHA-256
`5ba17b604338ca283144223c0a284858669cd38b9025413ca674162ec673d4a0`)
and
[`T53T53MachinQuotientCarry.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T53T53MachinQuotientCarry.lean)
(SHA-256
`d3725c0e4c818765b9bc9b8bf4a8716b916e2e025f18461963f5ef270c44dcba`)
are `machine-checked`.  The new automaton classification and separators below
remain `proof sketch`; they have not been promoted to the verified Lean
track.  This note makes no novelty claim and does not upgrade the route's
existing literature status.

## 1. Normalized target and quantifiers

The canonical V1 statement is

\[
 \forall m\in\mathbb N\;\forall w\in\{0,\ldots,9\}^m\;
 \exists n\in\mathbb N:\quad
 (d_n(\pi),\ldots,d_{n+m-1}(\pi))=w.              \tag{1}
\]

Digits are after the decimal point, leading zeroes in \(w\) are allowed,
and \(m=0\) is vacuous.  The occurrence must be contiguous.  The statement
does not assert a frequency, simple normality, or normality.

For the rest of the note, \(w\) is a fixed nonempty word.  “A state dies”
means that its emitted digit path has just completed a copy of (w).  This
is an automaton term, not a claim that a mathematical candidate has become
invalid for any unrelated reason.

## 2. Exact constant/tripling epochs

Put

\[
 d_j=12j+3,\qquad
 a_j=\max\{a:3^a\le d_j\},\qquad
 D_j=3^{a_j-1}.                                   \tag{2}
\]

T52 proves that (D_j) is exactly the complete three-primary part of the
reduced denominator of the sampled Machin phase at (j\ge1).  Since
(d_{j+1}-d_j=12),

\[
                    {D_{j+1}\over D_j}\in\{1,3\}. \tag{3}
\]

For a fixed exponent (a\ge2), the first index of its epoch is

\[
 J_a=\left\lceil{3^a-3\over12}\right\rceil.       \tag{4}
\]

Writing (D=3^{a-1}), its exact length is

\[
 L_a=J_{a+1}-J_a=
 \begin{cases}
 (D+1)/2,&a\text{ odd},\\
 (D-1)/2,&a\text{ even}.
 \end{cases}                                      \tag{5}
\]

Indeed, (3^a\equiv3\pmod {12}) for odd (a) and
(3^a\equiv9\pmod {12}) for even (a).  Equations (4)--(5) follow by
taking the first integer in the progression (12j+3) above the threshold.
In particular (L_a=2J_a+1) for odd (a) and (L_a=2J_a-1) for even
(a).

For (D\ge9), the multiplicative order of 10 modulo (D) is

\[
                     \operatorname{ord}_{D}(10)=D/9.          \tag{6}
\]

This follows from the elementary LTE identity
(v_3(10^n-1)=2+v_3(n)).  A constant epoch therefore lasts about (9/2)
cycles of the label permutation.  Repetition of the label alone is not
repetition of the output, because the reference phase and its fine carry
remain time-dependent.

## 3. Exact relative-label state map

Let

\[
 x_j={b_j\over Q_j}\in[0,1),\qquad
 Q_j=F_jD_j,\qquad (F_j,D_j)=1,                  \tag{7}
\]

be the fractional sampled Machin phase in lowest terms, with (D_j) the
complete three-primary factor.  The full local candidate grid which keeps
the actual non-three numerator residue is

\[
 z_{j,t}=\left\{x_j+{t\over D_j}\right\},qquad
 t\in\mathbb Z/D_j\mathbb Z.                     \tag{8}
\]

On the displayed (Q_j)-grid its numerator is

\[
                    b_j+tF_j\pmod {Q_j},          \tag{9}
\]

so every member has exactly the same residue modulo (F_j).

Write the exact rational Machin forcing as

\[
 \Delta_j=y_{j+1}-10y_j,qquad
 x_{j+1}=\{10x_j+\Delta_j\},                     \tag{10}
\]

where (y_j=10^jM_{3j}).  Put
(gamma_j=D_{j+1}/D_j\in\{1,3\}).  Direct substitution in (8) gives the
exact transition

\[
 \boxed{
 \{10z_{j,t}+\Delta_j\}=z_{j+1,\phi_j(t)},\qquad
 \phi_j(t)=10\gamma_jt\pmod {D_{j+1}}.}           \tag{11}
\]

Consequently:

- if (D_{j+1}=D_j), then (phi_j(t)=10t) is a permutation;
- if (D_{j+1}=3D_j), then (phi_j(t)=30t) is an injection whose image is
  exactly the residues divisible by 3 in
  (mathbb Z/(3D_j)\mathbb Z).

The other two cosets at a tripling threshold are new **local** quotient
choices, but they have no predecessor consistent with (10).  Treating the
threshold as a three-way branch would therefore be incorrect.

Starting at (J), the closed form is

\[
 t_j={D_j\over D_J}10^{j-J}t_J\pmod {D_j}.         \tag{12}
\]

There are exactly (D_J) inherited paths at every later scale.  Starting
at the first seed leaves only the three translations (0,1/3,2/3); a late
restart leaves (D_J=\Theta(J)) paths.  Neither count identifies which path
is the actual one.

## 4. Coupling to T53 and the forbidden-word automaton

At time (j), write the numerator of (z_{j,t}) as

\[
 b_{j,t}=F_jc_{j,t}+r_j,\qquad 0\le r_j<F_j,\qquad
 0\le c_{j,t}<D_j.                                \tag{13}
\]

Equation (9) makes (r_j) independent of (t).  T53 gives

\[
 \kappa_j=\left\lfloor{10r_j\over F_j}\right\rfloor,
 \qquad
 \delta_j(t)=\left\lfloor{10c_{j,t}+\kappa_j\over D_j}\right\rfloor,
 \qquad
 c^{\rm raw}_{j,+}(t)=(10c_{j,t}+\kappa_j)\bmod D_j.          \tag{14}
\]

Here (delta_j(t)) is exactly the next decimal digit emitted by
(z_{j,t}).  The raw state in (14) is multiplication by ten at the current
rational denominator; equation (11) then incorporates the Machin correction
and the possible denominator change.

Let ({\cal A}_w) be the usual prefix/KMP automaton for (w), with state
(q\in\{0,\ldots,|w|-1\}) recording the longest suffix which is a prefix of
(w).  Completing (w) sends a path to the dead state.  The exact live-state
map is therefore

\[
 (t,q)\longmapsto
 \left(\phi_j(t),
       {\cal A}_w(q,\delta_j(t))\right),           \tag{15}
\]

followed by deletion if the second coordinate completes (w).

For a fixed starting scale, (15) is deterministic and injective before
deletion.  Its live sets are nested and their cardinalities are
nonincreasing.  This is the only unconditional monotonicity found.  Within
an epoch the first coordinate is a permutation, so there is no state-count
contraction without using the time-dependent actual digits in (14).  At a
tripling threshold the inherited image has index three, but adding the two
fresh cosets would discard backward consistency; it cannot be used to
average the actual inherited state.

The exact finite checker below finds surviving labels on every complete
epoch tested.  Finite survival is not an asymptotic theorem, but it
falsifies any assertion that the transition shape itself deletes every
state in one epoch.

## 5. Infinite structural separator

This construction retains the exact (D_j) schedule and exact T53 form but
uses a different positive forcing.  Fix (J\) with (27\mid D_J), choose
(a\in\{1,\ldots,8\}), let (A=5\cdot239), and put

\[
 F_j=A^{j-J+2},\qquad
 \varepsilon_j={1\over D_jF_j},\qquad
 z_j={a\over9}-\varepsilon_j,qquad j\ge J.        \tag{16}
\]

The displayed fraction has numerator

\[
 b_j={aD_jF_j\over9}-1.                           \tag{17}
\]

It is congruent to (-1) modulo (F_j) and, because (27\mid D_j), to
(-1) modulo 3.  Hence (16) is reduced and its complete three-primary
denominator is exactly (D_j).

Define

\[
 \Delta_j^*=10\varepsilon_j-\varepsilon_{j+1}>0. \tag{18}
\]

Since (F_{j+1}=AF_j) and (D_{j+1}/D_j\in\{1,3\}), this forcing is
positive, geometric, and summable.  Moreover

\[
                  z_{j+1}=\{10z_j+\Delta_j^*\}.   \tag{19}
\]

The exact quotient split is

\[
 r_j=F_j-1,qquad c_j={aD_j\over9}-1.             \tag{20}
\]

T53 now gives

\[
 \kappa_j=9,qquad
 \delta_j=a,qquad
 (10c_j+9)\bmod D_j=c_j.                          \tag{21}
\]

At a denominator transition with
(gamma_j=D_{j+1}/D_j),

\[
 c_{j+1}=\gamma_j(c_j+1)-1,qquad
 {c_{j+1}+1\over D_{j+1}}={c_j+1\over D_j}={a\over9}.         \tag{22}
\]

Thus (c_j) is fixed in a constant epoch, changes by
(c\mapsto3c+2) at a tripling threshold, and has the exact normalized
invariant in (22).  Every output digit is (a).

For any nonempty (w), choose (a\in\{1,\ldots,8\}) with
(w\ne a^{|w|}).  The infinite output (aaaa\ldots) avoids (w).  This is
a separator for any proposed extinction argument which uses only the
nested three-primary modulus, positive summable coboundary forcing, T53, and
the constant/tripling state geometry.  It is not the actual Machin forcing
or numerator.

## 6. Whole-epoch separator with the actual Machin forcing

The preceding model can be strengthened from a forcing of the same form to
the exact numerical Machin forcing, at the price of constructing an
epoch-dependent state and relinquishing the actual non-three fine residue.

Let (x_j) be the actual phase and write (D_J=3^k).  T52 says

\[
                         v_3(x_j)=-k_j,qquad D_j=3^{k_j}.     \tag{23}
\]

Choose a rational (z_J) such that

\[
 v_3(z_J-x_J)>-k,qquad
 \left|z_J-{a\over9}\right|\le{1\over D_JH},       \tag{24}
\]

where (H) is an arbitrarily large integer prime to 3.  Such a point is
explicit.  If (x_J=b/(D_JF)) in lowest terms, take

\[
 z_J={n\over D_JH},qquad
 nF\equiv bH\pmod3,                               \tag{25}
\]

and choose (n) nearest to (aD_JH/9) in that residue class.  Consecutive
choices are spaced (3/(D_JH)).  When (27\mid D_J), taking the central
integer plus (1) or minus (1) gives error at most (1/(D_JH)), and the
congruence makes (n) a three-adic unit.  Thus (z_J) has exact
three-primary denominator (D_J), while (25) gives the first inequality in
(24).

Drive (z_j) by the actual forcing:

\[
                         z_{j+1}=\{10z_j+\Delta_j\}.           \tag{26}
\]

Both (z_j) and (x_j) obey (26).  Their difference at the next step is
ten times the preceding difference plus an integer.  Since (k_j) is
nondecreasing, induction and the ultrametric inequality give

\[
                         v_3(z_j-x_j)>-k_j.                    \tag{27}
\]

Combining (23) and (27) yields

\[
                         v_3(z_j)=-k_j                        \tag{28}
\]

at every later index, including tripling thresholds.  Hence the constructed
orbit retains the exact T52 three-primary denominator profile under the
actual forcing.

T46's exact telescope writes the accumulated forcing as

\[
 z_{J+s}=\{10^sz_J+R_{J,s}\},\qquad
 0\le R_{J,s}<10^s\rho^J,\qquad
 \rho={10\over625^3}.                             \tag{29}
\]

Because (10^sa/9\equiv a/9\pmod1), the circular distance from (z_{J+s})
to (a/9) is at most

\[
                         {10^s\over D_JH}+10^s\rho^J.         \tag{30}
\]

The point (a/9), for (1\le a\le8), is at distance at least (1/90)
from both boundaries of its digit cell.  On the epoch starting at (J_a),
equation (5) gives (L_a\le2J_a+1), so

\[
 10^{L_a}\rho^{J_a}\le10(100\rho)^{J_a}\longrightarrow0.   \tag{31}
\]

For every sufficiently late complete epoch, first make the second term in
(30) smaller than (1/180), then choose (H) so the first is smaller than
(1/180).  Equations (28)--(31) prove that every digit emitted throughout
the epoch, and also at its following tripling state if desired, is (a).
Choosing (a) with (w\ne a^{|w|}) gives a state which survives the entire
forbidden-word automaton.

This is a stronger separator than (16)--(22): the forcing values are the
actual ones.  Its exact limitation is equally important.  The auxiliary
factor (H) and the residue in (25) generally differ from the actual
(F_J,r_J).  Therefore (z_J) need not be one of the actual candidate-grid
members (8).  A contraction theorem which essentially exploits the exact
Machin fine residues is not separated by this construction.

## 7. Exact finite checks (`experiment`)

[`three_primary_automaton_check.py`](three_primary_automaton_check.py),
SHA-256
`9ea7b072a7dd36a07e2b83d4cb63613d65ea2f955777867f184a39f2e834bf16`,
uses only exact integers and `Fraction`.  It does not evaluate pi or read a
digit table.

Commands:

```bash
python3 -m py_compile \
  work/ultrapi-resume/three_primary_automaton_check.py
python3 work/ultrapi-resume/three_primary_automaton_check.py --max-j 80
```

Retained output:

```text
claim_status=experiment
source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
j_range=1..80
t52_three_primary_modulus_checks=81
constant_or_tripling_ratio_checks=80
exact_actual_forcing_translation_checks=8580
actual_fine_residue_preservation_checks=8580
t53_candidate_carry_checks=8580
transition_image_checks=80
complete_epoch_order_checks=3
forbidden_word_automaton_steps=15094
finite_actual_epoch_survivors=['a:3,j:2..6,D:9,word:0,survivors:5', 'a:3,j:2..6,D:9,word:00,survivors:9', 'a:3,j:2..6,D:9,word:012,survivors:9', 'a:3,j:2..6,D:9,word:314,survivors:9', 'a:3,j:2..6,D:9,word:999,survivors:9', 'a:4,j:7..19,D:27,word:0,survivors:7', 'a:4,j:7..19,D:27,word:00,survivors:25', 'a:4,j:7..19,D:27,word:012,survivors:27', 'a:4,j:7..19,D:27,word:314,survivors:27', 'a:4,j:7..19,D:27,word:999,survivors:27', 'a:5,j:20..60,D:81,word:0,survivors:1', 'a:5,j:20..60,D:81,word:00,survivors:54', 'a:5,j:20..60,D:81,word:012,survivors:76', 'a:5,j:20..60,D:81,word:314,survivors:77', 'a:5,j:20..60,D:81,word:999,survivors:76']
separator_complete_epochs=2
separator_exact_three_primary_steps=448
separator_constant_digit_steps=448
separator_t53_carry_steps=448
separator_exact_forcing_steps=432
structural_infinite_model_steps=592
structural_infinite_model_recurrences=592
structural_infinite_model_tripling_steps=16
constant_word_automaton_checks=6540
all exact checks passed
```

The first block checks (2)--(15) directly on exact Machin seeds, including
literal preservation of the actual numerator modulo (F_j).  The finite
survivor rows are `experiment` only.  The next block checks the whole-epoch
actual-forcing separator, its exact three-primary denominator, T53 digit,
and the following tripling transition.  The last block checks the infinite
structural model (16)--(22) through every constant and tripling step in the
finite range.  The algebra in Sections 5--6, not this finite run, is the
general separator.

## 8. Sharp remaining obligation

The exact actual-grid problem is now a finite deterministic question at
each late start (J): among the (D_J) labels in (8), prove that the one
actual path, or every inherited path if using extinction, cannot remain in
the live part of (15) indefinitely.

The following inputs are insufficient by themselves:

- (D_j=\Theta(j)) and its constant/tripling schedule;
- the fact that the label map is periodic within an epoch;
- a nonincreasing survivor count without strict contraction;
- T53's exact carry identities with an unrestricted fine state;
- positivity, summability, or even the exact numerical values of the Machin
  forcing when the non-three fine state is allowed to vary.

A result with genuine leverage must use the actual fine sequence
((F_j,r_j)) essentially.  Equivalent sufficient forms include a strict
contraction for the exact time-dependent automaton (15), a signed resonant
estimate for its actual inherited coset, or an archimedean theorem selecting
the true coarse quotient.  Merely summing all three cosets at a tripling
threshold would average in states with no consistent predecessor.

## Bottom line

The three-primary dynamics are now explicit: constant epochs permute,
tripling thresholds inject, and backward consistency never branches.  This
gives a clean finite-state formulation but no proof that survivor states die.
Explicit constant-digit orbits show that the modulus schedule, exact carry
form, and forcing structure do not create contraction on their own; even the
actual forcing admits arbitrarily long exact-three-primary avoiding epoch
states when the fine residue is varied.  The unresolved content is the
correlation of the actual Machin fine residue with its actual coarse state.
No cylinder hit, `candidate resolution`, or `verified resolution` follows.
