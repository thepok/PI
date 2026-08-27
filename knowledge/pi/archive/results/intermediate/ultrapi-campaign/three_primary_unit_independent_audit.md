# Independent audit: three-primary leading-unit attack

Date: 2026-08-12 UTC

## Scope and status

This audit checked:

- `work/ultrapi-resume/three_primary_unit_report.md`, SHA-256
  `a6b915e8fa2d9aa10a761c04b7270000c337736a4c62614f864f45cb5dd7b1a5`;
- `work/ultrapi-resume/three_primary_unit_check.py`, SHA-256
  `7002b39381a6eadd9251dce40b1616641b3deb3ce6584c85a9d9fde1b33868f1`;
- the new T55 selector formalization, SHA-256
  `97a7fabb52386ca91bd3fbd6a925e231733d2e2c0c404eb6fcdb1c0d40a291ba`.

Verdict: no substantive mathematical defect found.  The report correctly
keeps the shell and low-power calculations at `proof sketch`, the finite
checker output at `experiment`, and the generic selector identity at
`machine-checked`.  None of these claims proves V1.

## Formula audit

For a common odd exponent \(u=3^v s\), direct cancellation of the unique
factor three in \(4\cdot239^u-5^u=3G(u)\) gives

\[
  3^{a-1}P(u)=
  4\epsilon_u3^{a-v}\frac{G(u)}{s5^u239^u}.
\]

Hence a term survives modulo \(3^K\) exactly when
\(v\ge a-K+1\).  Writing \(H=3^{a-K+1}\) and \(u=Ht\), then
\(v_3(t)=s\), gives the factor \(3^{K-1-s}\) in formula (5).
Only residues modulo \(3^{s+1}\) matter after multiplication by this factor.

The two stabilization steps in (5) are valid.  For the cancellation
quotient one works before division by three, modulo \(3^{s+2}\).  The unit
group exponent is \(2\cdot3^{s+1}\), and

\[
  3^{a-K+1}t\equiv3^{s+1}\pmod {2\cdot3^{s+1}}.
\]

For the denominator unit modulo \(3^{s+1}\), its exponent group has exponent
\(2\cdot3^s\), and the actual exponent is congruent to \(3^s\) modulo that
number.  This proves the fixed exponents used in \(g_s\) and \(b_s\).
The stated independence from the chosen lifts also follows because any lift
error is divisible by \(3^{s+1}\), which the displayed power of three sends
to zero modulo \(3^K\).

At full precision \(K=a-1\), one gets \(H=9\), and the endpoint has valuation
\(a-1=K\), so the claimed reduction to common exponents divisible by nine is
correct.

## Low-power tables

Modulo three, only \(u=3^a\) survives.  Here \(G(u)\equiv-1\pmod3\), the
unit denominator is one, and
\((-1)^{(3^a-1)/2}=(-1)^a\).  Formula (6) follows.

For \(a\ge3\), the modulo-nine survivors are \(D,3D,5D,7D\), subject to
the three cutoff stages.  Direct modular evaluation gives
\(G(u)\equiv8\pmod9\), \(5^u239^u\equiv1\pmod9\), and
\(10^j\equiv1\pmod9\).  Summing the stage increments reproduces every entry
of table (7).  An independent evaluation of the stabilized \(K=3\) shell
also reproduced all eighteen entries of table (8).

## Selector identity

With \(Q=FD\), \(b=A\bmod Q\), \(r=b\bmod F\), and \(c=b/F\), Euclidean
division gives \(b=Fc+r\).  Reducing \(A\equiv b\pmod {FD}\) modulo \(D\)
and multiplying by \(F^{-1}\in\operatorname{ZMod}(D)\) yields

\[
  c\equiv AF^{-1}-rF^{-1}\pmod D.
\]

Since \(U=A/F\) in the localization at three, this is exactly report formula
(12).  T55 machine-checks the generic modular statement in three small
theorems; all are registered in `audit/AxiomAudit.lean`.  Their only axiom
dependencies are the repository allowlist `propext`, `Classical.choice`, and
`Quot.sound`.

## Reproduction and limitations

The default exact checker run reproduced all reported counts through
\(j=150\), \(K=6\), including 664 stabilized-shell comparisons and all six
coarse/fine residue classes.  The checker uses exact rational and modular
integer arithmetic.  A separate stress run through \(K=8\) passed 1,200 raw
shell and 1,200 reduced-numerator comparisons at the same 150 indices.

Those loops are finite `experiment`, not evidence that the formulas hold for
unbounded \(j\).  The proof sketches supply the general derivations, while
T55 formalizes only the generic selector identity.  In particular, neither
the report nor T55 controls the complementary phase \(rF^{-1}\); that phase
remains the explicit obstruction to extracting the actual coarse quotient.

Focused T55 compilation, the explicit axiom audit, and the full
`scripts/check.ps1` gate all passed.
