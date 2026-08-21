# Three-primary leading-unit attack

Date: 2026-08-12 UTC  
Target: canonical V1, every finite decimal word occurs contiguously in the
decimal expansion of \(\pi\)  
Source: `problems/local/pi-digits.txt`  
Original source URL: none recorded; the canonical source is a local,
human-authored root  
Source SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

## Status and bottom line

- `machine-checked`: for every integer \(j\ge1\), T52 proves the exact valuation
  \(v_3(q_j)=1-a_j\), where
  \(q_j=\operatorname{sampledMachinValueRat}(j)\) and
  \(3^{a_j}\le 12j+3<3^{a_j+1}\).
- `proof sketch`: the valuation argument can be sharpened to an exact finite
  shell formula for the leading unit
  \(U_j=3^{a_j-1}q_j\pmod {3^K}\).  For fixed \(K\), the formula has fewer
  than \(3^K/2+1\) terms, independent of the size of \(j\).  In particular,
  \(U_j\pmod3\) and \(U_j\pmod9\) have closed formulas.
- `machine-checked`: T55 proves the abstract exact selector identity in
  `ZMod D` for a denominator split \(F D\) with \(F\) invertible modulo \(D\).
- `proof sketch`: specializing that identity when
  \(q_j=A_j/(F_jD_j)\) is reduced with
  \(D_j=3^{a_j-1}\), the reduced numerator satisfies
  \(A_j\equiv F_jU_j\pmod {3^K}\).  The actual coarse quotient satisfies the
  exact selector identity
  \[
     c_j\equiv U_j-r_jF_j^{-1}\pmod {D_j}.
  \]
  Thus the full unit and the complementary phase together select \(c_j\),
  but the unit alone does not.
- `experiment`: 150 exact Machin seeds and all moduli \(3^K\),
  \(1\le K\le6\), passed the checker.  In each of the six classes determined
  by the parity of \(a_j\) and the three mod-nine shell stages, the actual
  values of both \(c_j\bmod3\) and \(r_jF_j^{-1}\bmod3\) attained all three
  residues by \(j=150\).

This is meaningful exact arithmetic progress, but it is not a proof of V1.
It exposes a cleaner obstruction: T52's leading unit is rigid, while the
non-three-primary phase supplies exactly the freedom that remains in the
actual coarse quotient.

## 1. Normalized arithmetic question

For an integer (j\ge1), put
\[
 d_j=12j+3,
 \qquad 3^{a_j}\le d_j<3^{a_j+1},
 \qquad D_j=3^{a_j-1},
 \qquad q_j=\operatorname{sampledMachinValueRat}(j).
\]
T52 gives \(v_3(q_j)=-(a_j-1)\), so
\[
                         U_j:=D_jq_j
\]
is a three-adic unit.  The questions attacked here are:

1. Can \(U_j\) be computed explicitly modulo growing powers of three?
2. Does that residue determine, or materially restrict, the actual coarse
   quotient \(c_j=\lfloor D_j\{q_j\}\rfloor\)?

The quantifier distinction is essential.  A formula modulo each fixed
\(3^K\) is not automatically uniform at the growing modulus
\(D_j=3^{a_j-1}\), and a finite computation is only an `experiment`.

## 2. Exact paired expansion

For an odd common Taylor exponent \(u\le d_j\), write
\[
 \epsilon_u=(-1)^{(u-1)/2},\qquad
 C(u)=4\,239^u-5^u,
 \qquad G(u)=\frac{C(u)}3.
\]
T52 proves that \(v_3(C(u))=1\), so \(G(u)\) is a three-adic unit.  The
combined common pair is
\[
 P(u)=
 \frac{4\epsilon_u C(u)}{u5^u239^u}.
\]
There is also the single base-239 endpoint at exponent \(d_j+2\).  The exact
seed expansion is
\[
 q_j=10^j\left(\sum_{\substack{1\le u\le d_j\\u\text{ odd}}}P(u)
       -\frac{4}{(d_j+2)239^{d_j+2}}\right).                 \tag{1}
\]
The endpoint sign is positive inside its Taylor term because its index
\((d_j+1)/2=6j+2\) is even; the Machin coefficient contributes the displayed
minus sign.

If \(v=v_3(u)\) and \(s=u/3^v\), direct cancellation gives
\[
 D_jP(u)=
 4\epsilon_u\,3^{a_j-v}\,
 \frac{G(u)}{s5^u239^u}.                                  \tag{2}
\]
Every denominator on the right of (2) is prime to three.

## 3. Finite shell formula modulo \(3^K\)

### `proof sketch`

Equation (2) shows that a common pair vanishes modulo \(3^K\) whenever
\(a_j-v_3(u)\ge K\).  Consequently only
\[
                 v_3(u)\ge a_j-K+1                         \tag{3}
\]
can contribute.  The endpoint vanishes as soon as \(a_j-1\ge K\).

For fixed \(K\) and \(a_j\ge K+1\), put
\[
 h=a_j-K+1,\qquad H=3^h,qquad L=\left\lfloor\frac{d_j}{H}\right\rfloor.
\]
The retained exponents are exactly \(u=Ht\), with \(t\le L\) odd.  Since
\(d_j<3^{a_j+1}\), one has \(L<3^K\), so there are fewer than
\(3^K/2+1\) terms.

For such an odd \(t\), put \(s=v_3(t)\) and \(t_0=t/3^s\).  Define the
local units
\[
 g_s\equiv
   \frac{4\,239^{3^{s+1}}-5^{3^{s+1}}}{3}
        \pmod {3^{s+1}},
 \qquad
 b_s\equiv(5\cdot239)^{3^s}\pmod {3^{s+1}}.                \tag{4}
\]
Then
\[
 \boxed{
 U_j\equiv10^j
 \sum_{\substack{1\le t\le L\\t\text{ odd}}}
 4(-1)^{(Ht-1)/2}3^{K-1-s}
 g_s\,t_0^{-1}b_s^{-1}pmod {3^K}.}                         \tag{5}
\]
Any lifts of \(g_s,b_s\) to residues modulo \(3^K\) may be used.  The
factor \(3^{K-1-s}\) makes (5) independent of those lifts.

The only input beyond (2) is Euler periodicity.  Modulo \(3^{s+2}\), the
actual exponent \(u=3^ht\) is congruent to \(3^{s+1}\) in the exponent
group; modulo \(3^{s+1}\), it is congruent to \(3^s\).  This gives the two
fixed exponents in (4).  The checker separately evaluates both the raw
shell from (2) and the stabilized formula (5).

At the full growing modulus \(K=a_j-1\), formula (5) is still valid: then
\(H=9\).  It computes \(U_j\pmod {D_j}\) using precisely the common
exponents divisible by nine.  This is an exact reduction, but it still has
\(\Theta(j)\) terms; it is not an asymptotic cancellation theorem.

## 4. Closed low-power residues

### Modulo three

### `proof sketch`

Taking \(K=1\) leaves only \(u=3^{a_j}\).  Since
\(G(u)\equiv-1\pmod3\), \(5^u239^u\equiv1\pmod3\), and
\((-1)^{(3^{a_j}-1)/2}=(-1)^{a_j}\),
\[
 \boxed{U_j\equiv(-1)^{a_j+1}\pmod3.}                       \tag{6}
\]
Thus \(U_j\equiv1\pmod3\) for odd \(a_j\), and
\(U_j\equiv2\pmod3\) for even \(a_j\).

### Modulo nine

### `proof sketch`

For \(a_j\ge3\), only
\[
 u=D_j,\quad3D_j,\quad5D_j,\quad7D_j
\]
can contribute, with the last two present only after the corresponding
cutoffs.  Here \(G(u)\equiv8\pmod9\),
\(5^u239^u\equiv1\pmod9\), and \(10^j\equiv1\pmod9\).  Hence
\[
\begin{array}{c|ccc}
 &3D_j\le d_j<5D_j&5D_j\le d_j<7D_j&7D_j\le d_j<9D_j\\ \hline
 a_j\text{ odd} &1&4&7\\
 a_j\text{ even}&8&5&2
\end{array}                                                     \tag{7}
\]
is the exact value of \(U_j\pmod9\).

For one further explicit check, take \(K=3\), \(a_j\ge4\),
\(h=a_j-2\), and \(L=\lfloor d_j/3^h\rfloor\).  The following table gives
\(10^{-j}U_j\pmod {27}\); an entry persists until the next odd cutoff.

\[
\begin{array}{c|rrrrrrrrr}
\text{largest odd cutoff}&9&11&13&15&17&19&21&23&25\\ \hline
h\text{ even}&17&8&26&23&5&14&20&11&2\\
h\text{ odd}&10&19&1&4&22&13&7&16&25
\end{array}                                                     \tag{8}
\]

## 5. Reduced numerator and coarse quotient

Write the reduced rational as
\[
 q_j=\frac{A_j}{Q_j},\qquad Q_j=F_jD_j,qquad(F_j,D_j)=1.
\]
Then, exactly in the localization at three,
\[
                         U_j=\frac{A_j}{F_j}.                 \tag{9}
\]
Therefore formula (5) also gives the reduced numerator congruence
\[
                 \boxed{A_j\equiv F_jU_j\pmod {3^K}.}        \tag{10}
\]
This is as far as the leading-unit calculation goes without controlling
the complementary denominator \(F_j\).  T52 determines its three-adic
valuation, not \(F_j\pmod {3^K}\).

For the fractional state, let
\[
 b_j=A_j\bmod Q_j,qquad
 r_j=b_j\bmod F_j,qquad
 c_j=\frac{b_j-r_j}{F_j},qquad0\le c_j<D_j.                  \tag{11}
\]
Multiplying
\(A_j/Q_j=\lfloor q_j\rfloor+b_j/(F_jD_j)\) by \(D_j\) gives
\[
 U_j=D_j\lfloor q_j\rfloor+c_j+\frac{r_j}{F_j}.
\]
Reduction modulo \(D_j\) yields the exact selector, whose generic modular
form is machine-checked in T55,
\[
 \boxed{c_j\equiv U_j-r_jF_j^{-1}\pmod {D_j}.}               \tag{12}
\]
Because \(0\le c_j<D_j\), (12) selects \(c_j\) uniquely once both terms
on the right are known.

Equation (12) is also the obstruction.  The leading unit is rigid, but the
fine phase \(r_jF_j^{-1}\) is precisely the missing coordinate.  Low-power
unit information alone does not select the low-power coarse quotient.

## 6. Exact falsification results

### `experiment`

The reproducible checker is
`work/ultrapi-resume/three_primary_unit_check.py`.  Its default run used
\(1\le j\le150\) and \(1\le K\le6\), and reported:

```text
exact_three_primary_valuation_checks=150
unit_mod_three_formula_checks=150
unit_mod_nine_stage_formula_checks=149
raw_finite_shell_formula_checks=900
stabilized_epoch_shell_formula_checks=664
reduced_numerator_congruence_checks=900
coarse_selection_identity_checks=150
scaled_unit_recurrence_checks=149
forcing_mod_nine_sparse_pattern_checks=148
```

For each of the six pairs
\[
 (a_j\bmod2,\;\text{one of the three stages in (7)}),
\]
the checker found
\[
 \{c_j\bmod3\}=\{0,1,2\},\qquad
 \{r_jF_j^{-1}\bmod3\}=\{0,1,2\}.                            \tag{13}
\]
This is finite evidence only.  It nevertheless falsifies any proposed
universal rule saying that the parity/stage data, or the corresponding
value of \(U_j\pmod9\), fixes \(c_j\pmod3\).

A small exact witness occurs inside one fixed epoch.  At
\(j=11,12,13\), all three seeds have
\[
 a_j=4,\qquad D_j=27,qquad U_j\equiv5\pmod9,
\]
while their coarse quotients are respectively
\[
                    c_j=26,21,25,
\]
which represent \(2,0,1\pmod3\).  The varying fine phase in (12), not the
T52 unit, accounts for the difference.

### `proof sketch`

Algebraically, the scaled quantities satisfy the exact recurrence.  If
\(f_j=q_{j+1}-10q_j\) and \(\gamma_j=D_{j+1}/D_j\in\{1,3\}\), then
\[
 U_{j+1}=10\gamma_jU_j+D_{j+1}f_j.                            \tag{14}
\]
The checker verifies (14) for the displayed finite range.  The recurrence
itself follows by substituting the definitions, but the forcing term contains the same
complementary arithmetic and does not close on the leading unit alone.

The mod-nine forcing nevertheless has an exact sparse pattern.  Away from
an epoch tripling, \(D_{j+1}=D_j\).  Then
\[
 D_jf_j\equiv
 \begin{cases}
 0&\text{if no shell cutoff is crossed},\\
 3&\text{if a cutoff is crossed and }a_j\text{ is odd},\\
 6&\text{if a cutoff is crossed and }a_j\text{ is even}
 \end{cases}
 \pmod9.                                                       \tag{15}
\]
At the tripling \(D_{j+1}=3D_j\), the residue is \(5\pmod9\) for odd
\(a_j\) and \(4\pmod9\) for even \(a_j\).  This is a useful exact
across-epoch recurrence, but it is a recurrence for the three-adic unit,
not for the archimedean coarse quotient.

## 7. Consequence for the proof search

### `proof sketch`

The useful gain is a precise separation:

1. the three-primary leading unit is explicitly computable by a bounded
   shell at every fixed precision;
2. at full precision it reduces to the exponents divisible by nine;
3. the coarse quotient is then the difference between that unit and the
   complementary phase.

The route does not currently yield a contraction, a forbidden-word hit, or
an archimedean bound.  A continuation would need new control of
\(r_jF_j^{-1}\pmod {3^K}\), or a joint theorem showing cancellation between
that phase and (5).  More refinements of T52 that ignore the complementary
phase cannot determine the actual coarse quotient, as equation (12) and
the exact witnesses already demonstrate.

No `candidate resolution` or `verified resolution` is claimed.
