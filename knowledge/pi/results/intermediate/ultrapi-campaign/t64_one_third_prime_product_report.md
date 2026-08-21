# T64 one-third-band Hutton prime product

Date: 2026-08-12 UTC

Claim status: `machine-checked` for the declarations listed below.  Direct,
aggregate, axiom-audit, independent-check, and full verification-gate runs
pass. No decimal-cylinder hit or V1 theorem is claimed.

## Statement

Put \(R=4K+3\) and let \(H_K\) be the rational lower Hutton shadow from T58.
If \(p\) is prime, \(p>7\), \(p\ne17\), and

\[
R<3p,\qquad p\le R,
\]

then

\[
v_p(H_K)=-1,
\qquad
v_p(\operatorname{den}(H_K))=1.
\]

Consequently, if

\[
G_K^{(1/3)}=
\prod_{\substack{p\le R\\p\ {m prime},\ p>7,\ p\ne17\\R<3p}}p,
\]

then \(G_K^{(1/3)}\mid\operatorname{den}(H_K)\).

## New point beyond T61--T62

T61 isolated the singular Taylor exponent using \(R<2p\). Every Hutton
exponent is odd. Under the weaker condition \(R<3p\), a positive multiple of
\(p\) below \(3p\) can only be \(p\) or \(2p\), while \(2p\) is even.
Therefore the only divisible Hutton exponent is still \(p\). The singular
pair and its noncancellation residue are exactly those already proved in T61;
all remaining terms have nonnegative \(p\)-adic valuation. T62's pairwise
coprime finite-product lemma then combines the individual divisors.

## Verified declarations

The module
`TheoryLib/PiQuantitativeBlockHitting/T64T64HuttonOneThirdPrimeProduct.lean`
contains and prints the axioms of eleven declarations:

1. `oneThirdPrime_not_dvd_other_hutton_exponent`;
2. `padicValRat_huttonRegularBlockRat_nonneg_oneThird`;
3. `padicValRat_huttonLowerRat_oneThirdPrime`;
4. `oneThirdPrime_dvd_huttonLowerRat_den`;
5. `padicValNat_huttonLowerRat_den_oneThirdPrime`;
6. `huttonOneThirdPrimeSet`;
7. `huttonOneThirdPrimeProduct`;
8. `mem_huttonOneThirdPrimeSet_iff`;
9. `huttonOneThirdPrime_dvd_huttonLowerRat_den`;
10. `huttonOneThirdPrimeSet_pairwise_coprime`;
11. `huttonOneThirdPrimeProduct_dvd_huttonLowerRat_den`.

The module is imported by `TheoryLib.lean`, and every declaration is
registered explicitly in `audit/AxiomAudit.lean`. Direct module compilation
and the complete direct axiom audit pass. The printed dependency set is only
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`, custom axiom,
`native_decide`, unsafe declaration, or opaque proof shortcut appears.

Independent adversarial review also passed.  It checked the strict lower and
inclusive upper endpoints, the elimination of cofactors \(0,1,2\), concrete
boundary cases, multiplicity one, product assembly, registrations, forbidden
constructs, and the complete verification gate.  The audited module SHA-256
is `c1a40fe144a954bf5f6570d19700262c11a8e8e31d9a0f66a34d3d9b2dce6ab9`.
The review is in `t64_independent_audit.md`, and its independent Lean replay is
`t64_independent_checks.lean`.

## Exact limitation

This strengthens the forced squarefree denominator band from
\((R/2,R]\) to \((R/3,R]\). It does not estimate the product asymptotically,
control the actual numerator in an Archimedean metric, distribute the short
decimal orbit, establish a supplied cylinder-containment premise, or prove
that any word occurs in \(\pi\). Those remain separate obligations.
