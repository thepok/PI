# Independent audit: BBP odd cofactor and exact-kill no-go

Audit date: **2026-08-13 UTC**

Verdict on the corrected frozen pair: **PASS**.  The square-root cofactor
bound, the exact 5-adic denominator, the exact-kill no-go, every retained
finite `experiment`, and the corrected hypothesis
(n\ge\max(4,e)) in equation (18) were independently reproduced.  An initial
audit found that the former hypothesis (n\ge e) omitted the integrality
condition (A_n\in\mathbb Z); the primary report was corrected before this
final verdict.  No proportional-row result was invalidated.

The audited infinite claims retain status `proof sketch`, and all bounded
calculations below have status `experiment`.  This audit is not
`machine-checked`, a `candidate resolution`, or a `verified resolution`.
No fixed-sixteen return was proved, and canonical V1 remains a `conjecture`.

## 1. Frozen scope and provenance

The target is
[problems/local/pi-digits.txt](../../problems/local/pi-digits.txt), SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
It is Marcel's immutable local question and has no external source URL; none
is invented here.

The exact frozen primary pair is:

- [bbp_odd_cofactor_short_orbit_experiment_20260813.md](bbp_odd_cofactor_short_orbit_experiment_20260813.md),
  SHA-256
  `c648520d7c118ed63326afffce407a05ff2b05ca69efae36caeb20d1a06851c3`;
- [bbp_odd_cofactor_short_orbit_experiment_20260813_check.py](bbp_odd_cofactor_short_orbit_experiment_20260813_check.py),
  SHA-256
  `5f35c22f15f65dc8ca979908dbf58e7c88879d022287ee480821f5f88fb4b664`.

The pinned parent is
[bbp_actual_odd_quotient_attack.md](bbp_actual_odd_quotient_attack.md),
SHA-256
`d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc`.

The independent checker is
[bbp_odd_cofactor_short_orbit_experiment_20260813_independent_check.py](bbp_odd_cofactor_short_orbit_experiment_20260813_independent_check.py),
SHA-256
`3912cad4ba139c966447d3e7ca48b10b53e9ca439496672ff669451bf0a12f26`.
It imports no primary checker and reconstructs the large-prime coordinates
directly from the four original partial fractions.

## 2. Independent square-root cofactor derivation

Use the reduced form and odd coordinate from the parent report:

\[
 B_M=\frac{P_M}{2^{K_M}R_M},\qquad
 \frac{c_M}{R_M},\qquad (c_M,R_M)=1,                 \tag{A1}
\]

where (R_M) is odd, and put (X=8M+5).  For a cutoff (Y\ge1), define

\[
 S_M(Y)=\prod_{\substack{p\mid R_M,\ p>Y\\p^2>X}}p,
 \qquad C_M(Y)=\frac{R_M}{S_M(Y)}.                   \tag{A2}
\]

If (p^2>X), then no one of

\[
 2k+1,\quad4k+3,\quad8k+1,\quad8k+5
 \qquad(0\le k\le M)                                \tag{A3}
\]

is divisible by (p^2).  Thus the least common denominator of the summands
has (p)-exponent at most one.  Reduction of the complete sum can delete
that factor but cannot increase it.  Every selected prime in (A2) therefore
has exponent exactly one, and ((S_M(Y),C_M(Y))=1).

For the square-root choice (Y=\lfloor\sqrt X\rfloor), (A2) deletes every
surviving prime strictly above (\sqrt X).  Consequently

\[
             P^+(C_M^\square)\le\sqrt X.             \tag{A4}
\]

The multiplicity bound also checks out independently.  For (p>5), two of
the four factors in (A3) cannot be divisible by (p) at the same index: all
pairwise resultants have prime support contained in (\{2,3,5\}).  Across
all indices, the denominator of a sum divides the least common multiple of
the summand denominators, so

\[
             v_p(R_M)\le\lfloor\log_pX\rfloor
             \qquad(p>5).                            \tag{A5}
\]

For each fixed prime (3) or (5), the crude four-factor estimate is
(O(\log X)).  Hence

\[
\begin{aligned}
 \log C_M^\square
 &\le \sum_{\substack{p\le\sqrt X\\p>5}}
       \lfloor\log_pX\rfloor\log p+O(\log X)\\
 &\le \vartheta(\sqrt X)
       +\sum_{\ell\ge2}\vartheta(X^{1/\ell})+O(\log X)\\
 &=O(\sqrt X\log X)=O(\sqrt M\log M)=o(M).          \tag{A6}
\end{aligned}
\]

The final estimate needs only the elementary Chebyshev upper bound; the
extra factor (\log X) is a harmless bound for the number of nonempty
power layers.  This confirms the frozen support and height claims.

For completeness, the survival test is also exact.  Multiply the BBP partial
sum by (p).  Modulo (p), every nonsingular summand vanishes, while every
summand with one (p) in its denominator contributes its simple-pole
residue.  Therefore

\[
 p\mid R_M\quad\Longleftrightarrow\quad
 G_{M,p}\not\equiv0\pmod p.                          \tag{A7}
\]

On this event, multiplying by the factor (16) used in the odd-coordinate
normalization gives the stated additive coordinate.  The independent replay
computes (A7) directly from

\[
 \frac4{8k+1}-\frac2{8k+4}
 -\frac1{8k+5}-\frac1{8k+6},                         \tag{A8}
\]

without copying the primary formula for (G_{M,p}).  Among 399,421
large-prime singular tests, 559 residues cancel and 398,862 survive; every
surviving coordinate agrees with the reduced odd fraction.  These counts
have status `experiment`.

## 3. Complete 5-adic pole analysis

Fix (M\ge0), put (X=8M+5), and let

\[
                    e=\lfloor\log_5X\rfloor.         \tag{A9}
\]

Here (e\ge1).  No denominator in (A8) has 5-adic valuation above (e).
This is immediate for the first three odd parts from their ranges; for the
last fraction, (4k+3\le(X+1)/2<X).

The terms at exact valuation (-e) can be exhausted without an asymptotic
argument.

1. For (8k+1) and (8k+5), an odd multiplier (q) in
   (q5^e<5^{e+1}) is either (1) or (3).  Since
   (5^e\equiv5\pmod8) for odd (e) and (1\pmod8) for even (e), the
   multiplier (1) gives exactly

   \[
   k_1=
   \begin{cases}
      (5^e-5)/8,&e\text{ odd},\\
      (5^e-1)/8,&e\text{ even}.
   \end{cases}                                       \tag{A10}
   \]

   The multiplier (3) is congruent to (7) or (3\pmod8), so it fits
   neither linear form.  The inequality (5^e\le X) puts (k_1) inside
   (0\le k\le M), including the lower endpoint of every (e)-range.
2. Since (2k+1\le(X-1)/4<5^{e+1}/4), the only possible multiplier is
   (1).  This supplies

   \[
                         k_2=(5^e-1)/2               \tag{A11}
   \]

   precisely when (k_2\le M).
3. Since (4k+3<(5^{e+1}+1)/2), its only possible odd multiplier is also
   (1), but (4k+3\equiv3\pmod4) cannot equal
   (5^e\equiv1\pmod4).  There is no fourth candidate.

After multiplication by (5^e), the (k_1) term has residue (4\pmod5)
in either parity.  The optional (k_2) term comes from
(-1/(2(2k+1))) and has residue
(-1/2\equiv2\pmod5).  Finally, (16^{-k}\equiv1\pmod5).  The leading
residue of (5^eB_M) is consequently either (4) or (4+2\equiv1), never
zero.  Thus

\[
 v_5(B_M)=-e,
 \qquad v_5(R_M)=e=\lfloor\log_5(8M+5)\rfloor.       \tag{A12}
\]

This includes both transition endpoints and the optional-pole threshold.
The independent checker exhaustively tests 31 such boundary configurations
through (e=8), as well as (A12) for every (0\le M\le1000); those finite
checks have status `experiment`.

## 4. Exact-kill no-go and the corrected CRT split

For all four replay cutoffs and (M\ge48), the threshold exceeds (5).
Therefore the complete factor (5^e) remains in (C).  If
(\eta/C) is its reduced additive coordinate, then ((\eta,C)=1).

For every (n\ge1), exact annihilation implies

\[
 \frac{10^n-16}{16}\frac{\eta}{C}\in\mathbb Z
 \quad\Longrightarrow\quad C\mid(10^n-16).           \tag{A13}
\]

Indeed, clear the denominator (16C) and cancel (\eta) modulo (C).
But

\[
                  10^n-16\equiv-1\pmod5,             \tag{A14}
\]

so (A13) is impossible.  This proves the exact-kill no-go at every positive
exponent.  When (n\ge4), (A_n=(10^n-16)/16) is an integer, and the
stronger equivalence

\[
 A_n\frac\eta C\in\mathbb Z
 \quad\Longleftrightarrow\quad C\mid A_n
 \quad\Longleftrightarrow\quad10^n\equiv16\pmod C    \tag{A15}
\]

is valid.  Below (n=4), the middle divisibility statement is not an
ordinary integer divisibility statement, so (A13), rather than (A15), is the
correct all-(n) formulation.  The frozen no-go conclusion remains valid.

Likewise (10^n\equiv1\pmod9), so

\[
 v_5(10^n-16)=0,\qquad v_3(10^n-16)=1.               \tag{A16}
\]

The frozen unavoidable missing factor in every gcd diagnostic follows.

Now write (C=5^eC_0) and choose CRT residues

\[
 \beta_5\equiv\eta C_0^{-1}\pmod{5^e},\qquad
 \beta_0\equiv\eta(5^e)^{-1}\pmod{C_0}.             \tag{A17}
\]

Their additive identity is

\[
 \frac\eta C\equiv\frac{\beta_5}{5^e}
                   +\frac{\beta_0}{C_0}\pmod1.       \tag{A18}
\]

Multiplication preserves a congruence modulo one when the multiplier is an
integer.  If (n\ge\max(4,e)), then (A_n\in\mathbb Z) and
(A_n\equiv-1\pmod{5^e}), so (A18) gives

\[
 A_n\frac\eta C
 \equiv-\frac{\beta_5}{5^e}
       +A_n\frac{\beta_0}{C_0}\pmod1.                \tag{A19}
\]

This is the corrected version of frozen equation (18).  It fully suffices
on the intended rows: for (M\ge48), every (n\ge M) is at least (4),
and (e\le M) (already (5^M\ge8M+5) for (M\ge3)).  Thus the 5-primary
phase is genuinely constant along each proportional row.

## 5. Correction audit and excluded counterexample

The initial frozen report stated (A19) under only (n\ge e).  At (n<4),
(A_n) is not an integer, so multiplying (A18) by (A_n) does not preserve a
congruence modulo one.  Worse, the right side then is not well-defined from
the residue class (\beta_0\pmod{C_0}): replacing (\beta_0) by
(\beta_0+C_0) changes it by the noninteger (A_n).  The corrected primary
report now states exactly (n\ge\max(4,e)), matching (A19).

An exact counterexample comes from the report's own square-root cofactor at
(M=48), not from an artificial modulus.  Here

\[
\begin{gathered}
 e=3,\qquad n=3\ge e,\qquad A_3=123/2,\\
 C=1058444843581125,\qquad
 \eta=852891167669146,\\
 \beta_5=79,\qquad \beta_0=1471632212207.
\end{gathered}                                       \tag{A20}
\]

With the least nonnegative representatives in (A20), the left side of the
former equation (18) minus its right side equals

\[
                              79/2,                  \tag{A21}
\]

which is not an integer.  This demonstrates why the correction was needed,
and the example is now excluded because (3<\max(4,3)).  The independent
checker pins the corrected primary text and tests (A19) on every intended
exponent.

## 6. Independent finite replay

Commands run from the repository root:

```text
python -m py_compile \
  work/ultrapi-resume/bbp_odd_cofactor_short_orbit_experiment_20260813_check.py \
  work/ultrapi-resume/bbp_odd_cofactor_short_orbit_experiment_20260813_independent_check.py
python \
  work/ultrapi-resume/bbp_odd_cofactor_short_orbit_experiment_20260813_check.py
python \
  work/ultrapi-resume/bbp_odd_cofactor_short_orbit_experiment_20260813_independent_check.py
```

Both replays completed.  The independent output is:

```text
status: PASS
finite_claim_label: experiment
audited_mathematical_claim_label: proof sketch
corrected_primary_domain: n >= max(4,e)
coefficient_identity_checks: 1001
five_pole_boundary_checks: 31
five_denominator_checks: 1001
possible_large_prime_checks: 399421
cancelled_large_prime_checks: 559
surviving_coordinate_checks: 398862
square_support_checks: 953
short_orbit_checks: 409640
crt_phase_checks: 409640
each cutoff: local_obstruction=948, compatibility_obstruction=5
exceptional_depths: 75, 76, 77, 78, 81
independent_record_sha256:
  b1e85b85f100948b8b8b49c191df64975126c4aa34d64558c278e1f7c46a3682
asserts_fixed_sixteen_return: false
asserts_v1: false
```

The five selected square-root samples reproduce the primary values of
(\log C_M^\square/M), (P^+(C_M^\square)), and (v_5(C_M^\square)).
Every one of the 409,640 intended row phases satisfies the corrected CRT
identity (A19).  The classification counts and the five exceptional depths
also agree exactly.  These are finite `experiment` results, not an
asymptotic return or non-return.

The primary files were not changed.  Python compilation, exact hash pins,
both replays, Markdown-link checks, duplicate equation-label checks,
control-character checks, tab checks, and trailing-whitespace checks were
included in the audit.

## 7. Coordination record and conclusion

This audit registered the descendant-area watch
`watch:local:pi-digits:independent-odd-cofactor-audit-20260813` on
`local:pi-digits` for agent `codex-independent-odd-cofactor-audit`.  Its
initial and pre-verdict polls were empty at cursor and delivered sequence
57,062, so no event was acknowledged.  Observation events were treated only
as coordination signals and not as mathematical evidence.

**Final verdict: PASS.**  The corrected frozen pair uses the necessary domain
(n\ge\max(4,e)), and the square-root localization, exact 5-adic valuation,
exact-kill no-go, and rowwise constant 5-primary phase all withstand this
independent audit.  None of them proves the remaining weighted short-orbit
estimate, so V1 remains a `conjecture`.
