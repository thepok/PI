# T65 one-fifth-band Hutton prime product

Date: 2026-08-12 UTC

Claim status: `machine-checked` for the declarations listed below. Focused,
aggregate, direct-audit, independent-check, and full verification-gate runs
pass. No decimal-cylinder hit or V1 theorem is claimed.

## Statement

Put \(R=4K+3\), and let \(H_K\) be the rational lower Hutton shadow from T58.
If \(p\) is prime, \(p>7\), \(p\ne10889\), and

\[
 R<5p,\qquad 3p\le R,
\]

then

\[
 v_p(H_K)=-1,
 \qquad
 v_p(\operatorname{den}(H_K))=1.
\]

The complete squarefree product over this exact band divides
\(\operatorname{den}(H_K)\).

## Proof structure

Every Hutton Taylor exponent is odd.  Below \(5p\), a positive odd multiple
of the odd prime \(p\) can only be \(p\) or \(3p\).  T65 erases exactly their
two Taylor indices and proves that all other terms are \(p\)-integral.

Combining the two base-3/base-7 pairs at exponents \(p\) and \(3p\) produces
the exact factor

\[
 C_p=3(2\cdot7^p+3^p)3^{2p}7^{2p}
      -(2\cdot7^{3p}+3^{3p}).
\]

Fermat reduction gives

\[
 C_p\equiv21778=2\cdot10889\pmod p.
\]

Therefore the four-term singular block has valuation \(-1\) for \(p>7\)
outside \(p=10889\).  The ultrametric inequality then retains that valuation
after adding the regular block.  Reduced-numerator coprimality converts it to
exact denominator multiplicity one.  Pairwise coprimality combines all
individual divisors into the finite product theorem.

## Verified declarations

The module
`TheoryLib/PiQuantitativeBlockHitting/T65T65HuttonOneFifthPrimeProduct.lean`
contains and prints the axioms of 26 declarations, including the two singular
indices/blocks, fixed-residue factorization, Fermat reduction, noncancellation,
exact decomposition, regular-block integrality, valuation, denominator
multiplicity, exact finite set, pairwise coprimality, and product divisibility.
Every declaration is imported through `TheoryLib.lean` and explicitly
registered in `audit/AxiomAudit.lean`.

Direct compilation and the complete direct audit report only `propext`,
`Classical.choice`, and `Quot.sound`.  The module contains no `sorry`,
`admit`, new axiom, `native_decide`, unsafe declaration, or opaque proof
shortcut.

Independent adversarial review also passed.  It rederived the four-term
fraction and residue, checked both band endpoints, the erased-index argument,
the admissible exceptional case \(K=8166\), exact multiplicity and product
assembly, all 26 registrations, and the full gate.  The audited module SHA is
`5abbbccd8b6cde2296edad23644709f1f714c7a0408dc6003b796645b8c045d9`.
The audit is `t65_independent_audit.md`, with concrete replay in
`t65_independent_checks.lean`.

Scope caveat: T65 proves noncancellation and survival outside \(10889\), and
its checks prove that \(10889\) is the unique admissible fixed-residue
exception.  T65 does not itself declare that the prime is absent from the full
reduced denominator at the exceptional instance; that stronger statement is
part of the separately audited general multi-band `proof sketch`.

## Exact limitation

Together with T64, the new finite theorems force every eligible prime in
\((R/5,R]\), except the fixed primes 17 and 10889 in their respective bands,
to occur once in the reduced Hutton denominator.  A prime-number-theorem
evaluation would give logarithmic mass \(4R/5+o(R)\), but that asymptotic is
not a T65 declaration.  Neither the finite divisor theorem nor that standard
asymptotic controls the actual numerator, the complementary CRT phase, a
short decimal orbit, a cylinder-containment witness, or V1.
