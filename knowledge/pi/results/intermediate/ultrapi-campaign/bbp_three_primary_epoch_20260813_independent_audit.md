# Independent audit: BBP three-primary denominator epochs

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
<code>2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825</code>.
The target is Marcel's immutable local question and has no external source
URL; none is invented here.

Audited artifacts:

- [bbp_three_primary_epoch_20260813.md](bbp_three_primary_epoch_20260813.md),
  SHA-256
  <code>5b34ceb3aa2857b9227cce5ac7ae84cafbbac47d2c12adf889c37f11280d6fd7</code>;
- [bbp_three_primary_epoch_20260813_check.py](bbp_three_primary_epoch_20260813_check.py),
  SHA-256
  <code>4cb663d1d484c750ad99d2120d13143c24297ab4f81860a9f1584d5018ea2fa1</code>;
- the pinned Bourgain--Chang
  [PDF](../theory/pi-lacunary-near-return-sparsity/library/t124/bourgain-chang-2006.pdf),
  SHA-256
  <code>a4c130e401ff03a5b91fbd20339f06021f26bf871ca2bb375f2ce25e3ee5d1d7</code>.

Independent checker:
[bbp_three_primary_epoch_20260813_independent_check.py](bbp_three_primary_epoch_20260813_independent_check.py),
SHA-256
<code>c15ef949abc0d2f3f0cd7331bccd2fb8ecf0a4109142091427f1438aaafd9e8f</code>.
It imports no code from the primary checker.

## Verdict and claim boundary

**Independent audit verdict: PASS.** No fatal gap was found in the exact
three-primary epoch formula, its one-level cancellation, the residual-orbit
bijection, the proportional-row inequalities, or the stated
Bourgain--Chang applicability obstruction.

The all-depth argument retains status <code>proof sketch</code>. The
independent bounded replay has status <code>experiment</code>. The direct,
dated inspection of the pinned Bourgain--Chang source has status
<code>literature-checked</code>. Nothing in this audit is
<code>machine-checked</code>.

In particular, a complete grid in one CRT coordinate is not a return of the
full BBP phase. This audit does **not** prove that every finite decimal word
occurs in pi. Canonical V1 remains a <code>conjecture</code>.

One nonfatal editorial normalization is worth recording. If \(K_M\) in the
primary report's factorization is intended to be the exact two-primary
denominator exponent, uniqueness would be clearer with
\((S_M,6)=1\), rather than only \((S_M,3)=1\). The three-primary proof uses
only that \(2^{K_M}S_M\) is a 3-adic unit, so no audited result depends on
this wording.

## 1. Independent derivation of every epoch

Start directly from the four partial fractions

\[
 \frac4{8k+1}-\frac1{2(2k+1)}
 -\frac1{8k+5}-\frac1{2(4k+3)}.                 \tag{A1}
\]

Let \(P=3^e\). A pole \(ak+b=qP\) has exact height \(e\) precisely when
\(3\nmid q\). Solving the four elementary congruences for \(q\) gives

\[
\begin{array}{c|cc}
\text{pole}&e\text{ odd}&e\text{ even}\\ \hline
8k+1&q\equiv3\pmod8&q\equiv1\pmod8\\
2k+1&q\equiv1\pmod2&q\equiv1\pmod2\\
8k+5&q\equiv7\pmod8&q\equiv5\pmod8\\
4k+3&q\equiv1\pmod4&q\equiv3\pmod4.
\end{array}                                                   \tag{A2}
\]

These classes reproduce the primary report's first-pole table: for odd
\(e\), the least 3-coprime quotients are \(11,1,7,1\); for even \(e\),
they are \(1,1,5,7\).

### 1.1 Odd epochs

For odd \(e\), put

\[
 D_e=\frac{P-3}{4},\qquad A_{e+1}=\frac{3P-1}{8}.
\]

At \(k=D_e\), the fourth pole is \(4D_e+3=P\). At the last allowed
depth \(M=A_{e+1}-1\), the four pole forms are bounded respectively by

\[
       3P-8,\quad \frac{3P-5}{4},\quad3P-4,
       \quad\frac{3P-3}{2}.                                  \tag{A3}
\]

Filtering (A3) through (A2), and excluding \(3\mid q\), leaves no
admissible quotient in the first three forms and only \(q=1\) in the
fourth. All four forms are below the first possible multiple of
\(3^{e+1}=3P\). Thus throughout the half-open interval

\[
                        D_e\le M<A_{e+1},                    \tag{A4}
\]

there is exactly one maximal-height pole. Its coefficient
\(-1/2\equiv1\pmod3\), so

\[
                         E_M=e,\qquad u_M=1.                 \tag{A5}
\]

This proves both uniqueness and the absence of a hidden higher pole; it is
not an inference from the transition table.

### 1.2 Even epochs before cancellation

For even \(e\), put

\[
 A=\frac{P-1}{8},\quad4A=\frac{P-1}{2},\quad
 5A=\frac{5(P-1)}8,\quad6A=\frac{3(P-1)}4.                  \tag{A6}
\]

At \(M=6A-1\), the four forms are strictly below
\(6P,2P,6P,3P\). The even classes in (A2) leave exactly

\[
 (8A+1)=P,\qquad2(4A)+1=P,\qquad8(5A)+5=5P,                \tag{A7}
\]

and no fourth-form pole. They arrive in that order. Their leading residues
are all \(1\pmod3\), so the cumulative leading units are \(1,2,0\).
Consequently the first two even stages have

\[
\begin{array}{c|cc}
A\le M<4A&E_M=e&u_M=1\\
4A\le M<5A&E_M=e&u_M=2.
\end{array}                                                   \tag{A8}
\]

The next record pole is \(4(6A)+3=3P=3^{e+1}\). Equations (A4) and
(A6) are adjacent: the end of an odd interval is the next even \(A\),
and the end of an even interval is the next odd \(D\). Starting at
\(D_1=0\), they are disjoint and cover every \(M\ge0\).

## 2. The cancellation is exactly one level

The question at \(M=5A\) is not merely whether the height-\(e\) residues
sum to zero modulo 3, but what survives one level lower.

### 2.1 The top cluster vanishes after division by 3

The three height-\(e\) terms form

\[
 H_e=4\,16^{-A}-\frac12\,16^{-4A}-\frac15\,16^{-5A}.
                                                                  \tag{A9}
\]

For every even \(e\ge2\), \(A\equiv4A\equiv1\pmod3\) and
\(5A\equiv2\pmod3\). Since \(16\equiv7\pmod9\), with inverse powers
\(7^{-1}\equiv4\) and \(7^{-2}\equiv7\), rational arithmetic in
\(\mathbb Z_{(3)}/9\mathbb Z_{(3)}\) gives

\[
 H_e\equiv4\cdot4-5\cdot4-2\cdot7=-18\equiv0\pmod9.       \tag{A10}
\]

Here \(5\) and \(2\) are the inverses of \(2\) and \(5\) modulo 9. Hence
\(H_e/3\equiv0\pmod3\). The old top cluster contributes nothing after
the sum is scaled by \(3^{e-1}\).

### 2.2 Complete lower-pole list

Let \(Q=3^{e-1}\), so \(Q\equiv3\pmod8\). At the cancellation depth

\[
                    5A=\frac{15Q-5}{8},                    \tag{A11}
\]

the four maximum normalized pole sizes are below, or at the indicated
endpoint,
\(15-4/Q,(15-1/Q)/4,15,(15+1/Q)/2\). Immediately before the next epoch they
are strictly below \(18,9/2,18,9\). Applying the odd classes in (A2) at
both endpoints produces the same complete list

\[
\begin{array}{c|c|c}
\text{pole}&q\text{ of exact height }e-1&
\text{localized residue mod }3\\ \hline
8k+1&11&11^{-1}=2\\
2k+1&1&-2^{-1}=1\\
8k+5&7&-7^{-1}=2\\
4k+3&1,5&-2^{-1}(1+5^{-1})=0.
\end{array}                                                   \tag{A12}
\]

All these poles are already present at \(M=5A\), and no new one appears
before \(6A\). Their sum is \(2\pmod3\). Terms of height at most
\(e-2\) vanish after multiplication by \(3^{e-1}\), while (A10) kills
the divided top cluster. Therefore

\[
                 E_M=e-1,\qquad u_M=2
                 \quad(5A\le M<6A).                         \tag{A13}
\]

This independently establishes the claimed exact one-level drop. It also
confirms the complete all-depth table, including the boundary cases
\(e=1\) and \(e=2\).

## 3. Residual period and coset bijection

For \(n\ge1\), \(10^n\equiv1\pmod9\), so

\[
 v_3(10^n-16)=1,\qquad
 g_n:=\frac{10^n-16}{3}\equiv1\pmod3.                      \tag{A14}
\]

If \(\beta_M\) is the primary report's primitive numerator modulo
\(3^{E_M}\), the reduced 3-primary row coordinate is therefore

\[
             \frac{\beta_Mg_n\bmod3^{E_M-1}}{3^{E_M-1}}.   \tag{A15}
\]

LTE gives

\[
                       v_3(10^h-1)=2+v_3(h).                \tag{A16}
\]

Thus \(10\) has exact order \(T_E=3^{E-2}\) modulo \(3^E\). Division by
3 is legitimate in the following equivalence:

\[
 g_n\equiv g_m\pmod{3^{E-1}}
 \iff10^n\equiv10^m\pmod{3^E}
 \iff n\equiv m\pmod{T_E}.                                 \tag{A17}
\]

A period contains \(T_E\) distinct values, all congruent to 1 modulo 3.
That is exactly the cardinality of the coset

\[
             \{1+3j:0\le j<T_E\}\pmod{3^{E-1}}.           \tag{A18}
\]

Multiplication by the 3-adic unit \(\beta_M\) is a bijection, so (A18)
becomes the claimed \(u_M\pmod3\) coset. Dividing by \(3^{E-1}\)
makes it a translated circle grid of spacing \(1/T_E\). Both the period
and the coset are exact, not upper bounds.

## 4. Proportional-row inequalities

The exact number of exponents in a row is

\[
 L_M=\lfloor M\log_{10}16\rfloor-M+1
    =\left\lfloor\log_{10}( (8/5)^M )\right\rfloor+1.       \tag{A19}
\]

Any \(T_E\) consecutive indices form one complete orbit by (A17), while a
shorter interval contains fewer than \(T_E\) distinct points. Hence full
coverage is equivalent to \(L_M\ge T_E\).

For an even epoch's last pre-drop row, with \(T=3^{e-2}\),

\[
       M=5A-1=\frac{45T-13}{8}\ge5(T-1).                   \tag{A20}
\]

For every even drop epoch \(e\ge4\), its reduced exponent is \(e-1\),
so \(T=3^{e-3}\), and

\[
       M\ge5A=\frac{135T-5}{8}>5(T-1).                     \tag{A21}
\]

Because \(8^5>10\cdot5^5\), (A19)--(A21) imply full coverage on all
these rows. Conversely, for odd \(e\ge5\), \(T=3^{e-2}\) and

\[
 M\le\frac{27T-9}{8}\le4(T-1).                             \tag{A22}
\]

Since \(8^4<10\cdot5^4\), (A19) and (A22) imply \(L_M<T\). Direct
integer calculation gives \(L_M=2<T=3\) for \(6\le M\le9\), the odd
\(e=3\) epoch. The odd \(e=1\) residual denominator is trivial. This
confirms every claimed positive and negative row-coverage statement.

## 5. Bourgain--Chang source check

### <code>literature-checked</code>

The pinned PDF was inspected directly on **2026-08-13 UTC**.

- At the start of Section 4, Bourgain--Chang write
  \(q=\prod p_\alpha^{\nu_\alpha}\) and define “few prime factors” by a
  uniform bound on \(\sum_\alpha\nu_\alpha\). Thus a modulus containing
  \(3^{E_M}\) leaves this hypothesis as \(E_M\to\infty\).
- Corollary 4.5 assumes
  \(\operatorname{ord}_p(\theta)>q^\delta\) for **every** prime
  \(p\mid q\). For \(\theta=10\) and \(p=3\), the left side is
  \(\operatorname{ord}_3(10)=1\), so the assumption fails.
- Corollary 4.2 and Theorem 4.7 remain within the same bounded-multiplicity
  modulus framework and therefore do not restore a uniform estimate for
  this family.

The primary report also correctly keeps the unreduced modulus. Combining a
primitive 3-primary coordinate \(\beta/3^E\) with a primitive high-prime
coordinate \(\xi/Q\) gives power coefficient

\[
                     A=\beta Q+\xi3^E\pmod{3^EQ}.           \tag{A23}
\]

Modulo 3 only \(\beta Q\) survives, and modulo every \(p\mid Q\) only
\(\xi3^E\) survives. Hence \((A,3^EQ)=1\). Reducing the denominator first
would replace the pure power \(10^n\) by
\((10^n-16)/3\), so it is not a direct application of Corollary 4.5.

Accordingly, the report's conclusion is appropriately narrow: the pinned
theorem does not simply absorb the unbounded 3-primary coordinate. This is
an applicability obstruction, not a theorem that all joint estimates are
impossible.

## 6. Independent bounded replay

The independent checker reconstructs each partial sum from (A1), not from
the primary checker's coefficient routine. It enumerates pole quotients by
solving \(ak+b=q3^e\), checks symbolic epochs through \(e=160\), evaluates
exact reduced partial sums through \(M=6200\), and enumerates residual
orbits through \(E=12\). Its output was:

~~~text
claim_status=experiment
coefficient_identity_checks=2049
symbolic_partition_checks=160
symbolic_pole_list_checks=1120
symbolic_cluster_checks=80
symbolic_row_inequality_checks=237
exact_fraction_state_checks=6201
exact_row_window_checks=6201
full_grid_rows=1533
nontrivial_odd_full_grid_rows=0
quotient_orbit_checks=11
quotient_orbit_points=88573
direct_localized_phase_checks=51
primitive_numerator_checks=19158
observed_state_transitions=0:E1/u1/odd,1:E2/u1/even-first,4:E2/u2/even-second,5:E1/u2/even-drop,6:E3/u1/odd,10:E4/u1/even-first,40:E4/u2/even-second,50:E3/u2/even-drop,60:E5/u1/odd,91:E6/u1/even-first,364:E6/u2/even-second,455:E5/u2/even-drop,546:E7/u1/odd,820:E8/u1/even-first,3280:E8/u2/even-second,4100:E7/u2/even-drop,4920:E9/u1/odd
v1_status=not_proved
status=PASS
~~~

These computations are an <code>experiment</code>; the finite cutoffs do not
prove the all-depth statements. The proof is the congruence and endpoint
derivation in Sections 1--4.

Reproduction from the repository root:

~~~bash
python work/ultrapi-resume/bbp_three_primary_epoch_20260813_independent_check.py
~~~

No <code>ultrapi.md</code>, Lean file, or verified-track file was edited by
this audit.

## 7. Coordination record

This audit registered descendant-area watch
<code>ultrapi-three-primary-independent-20260813</code> on
<code>local:pi-digits</code> for agent
<code>codex-ultrapi-three-primary-independent</code>. Its initial poll was
empty at cursor and delivered sequence 57,286. The final poll after all
artifact checks was also empty at the same cursor and delivered sequence, so
there was no event to acknowledge. Observation events are coordination
signals only and were not used as mathematical evidence.
