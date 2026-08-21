# Independent audit: Gauss--Lambert exceptional-gcd upper bound

Audit date: **2026-08-12 UTC**

Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)

Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

Primary artifact under audit:
[`gauss_exceptional_gcd_upper_bound_attack.md`](gauss_exceptional_gcd_upper_bound_attack.md)

Primary checker:
[`gauss_exceptional_gcd_upper_bound_check.py`](gauss_exceptional_gcd_upper_bound_check.py)

Independent checker:
[`gauss_exceptional_gcd_upper_bound_independent_check.py`](gauss_exceptional_gcd_upper_bound_independent_check.py)

## Verdict and claim status

**PASS after four narrow corrections and one prior-art correction.**  I found
no mathematical error in equations (3)--(34), including the signs in the
valuation argument, the exact iff (7), the strict small/large-prime split,
or the asymptotic equivalence (33).  I also checked the subsequently added
cutoff argument (28a)--(28e) and reduction (33a)--(33c); they are valid.

This is a `proof sketch`, not `machine-checked`.  The independent computations
below are an `experiment`.  The primary-source search is
`literature-checked` as of the audit date.  In particular, the Lucas product
(18) is **rediscovered prior art**, not a new theorem: it is a specialization
of Tony D. Noe's 2006 equation (13).  Neither the primary artifact nor this
audit proves \(\log E_n=o(n)\), the weaker constant bound, a decimal-cylinder
hit, or canonical V1.  V1 remains a `conjecture`; there is no `candidate
resolution` or `verified resolution` here.

## Corrections required by the independent audit

The frozen pre-audit report had SHA-256
`c17bc86915704cd50a572c0404075fdf079d41e9ffe6bb8f1526e889a1cf994a`;
its checker had SHA-256
`970594794acddb8d44336213631b005ae47922ae0842bf19009c4a8b58f63343`.
The following were corrected in the audited copies:

1. Equation (5) now explicitly quantifies \(n\ge2\); otherwise
   \(r_\ell(n-1)\) is undefined at \(n=1\).  Equations (10), (12)--(14),
   and (29) likewise received their natural domains.
2. The earlier-numerator block statement now assumes \(1\le a<\ell\).
   Without \(a\ge1\), its premise is vacuously triggered by \(P_0=0\), but
   the resulting depths are outside the strict large-prime range.
3. The earlier-denominator statement now records \(0\le s<\ell\); its
   premise itself excludes \(s=0,1\) because \(Q_0=Q_1=1\).
4. The primary checker's large-prime loop now uses the report's strict
   condition \(\ell<n\), rather than including the boundary \(\ell=n\).
   The PASS pair count consequently changes from 84,386 to 84,219; the 1,197
   exceptional pairs are unchanged.
5. The novelty wording and literature section now cite Noe and classify
   (17)--(19) as a self-contained rediscovery for this sequence.
6. The added definition (33a) now says explicitly that \(\ell\) is an odd
   prime, rather than relying on inheritance from the preceding set.

These were domain, checker-scope, and provenance defects.  They do not alter
the mathematical reduction after correction.

## First-principles equation audit

Throughout, \(n\ge1\) where factorials and \(E_n\) occur; \(n\ge2\) in (5)
and in asymptotics.  Let \(r=r_\ell(n)=\lfloor\log_\ell n\rfloor\), so
\(v_\ell(\operatorname{lcm}(1,\ldots,n))=r\).

### Normalization and valuations: (3)--(16)

- The previous denominator audit establishes that the divisor in (4) is
  integral.  For odd \(\ell\), the power of two is a unit and
  \(v_\ell(\operatorname{odd}(n!/L_n))=v_\ell(n!)-r\).  Since
  \(P_n=n!V_n\) and \(Q_n=n!U_n\),

  \[
  v_\ell(E_n)=r+\min(v_\ell(U_n),v_\ell(V_n)),
  \]

  which is exactly (13), including its sign.
- Every summand in (11) is \(\ell\)-integral for odd \(\ell\), so
  \(v_\ell(U_n)\ge0\).  In (10), every denominator is at most \(n\), hence
  its valuation is at most \(r\); the nonarchimedean triangle inequality
  gives (12), including possible cancellation in the favorable direction.
- Put \(m=\min(v_\ell(U_n),v_\ell(V_n))\) and
  \(r'=r_\ell(n-1)\).  In determinant (14), the first summand has valuation
  at least \(m\).  The second has valuation at least
  \(v_\ell(U_n)-r'\ge m-r'\).  Therefore the difference has valuation at
  least \(m-r'\).  Its exact value is \(-v_\ell(n)\), so
  \(-v_\ell(n)\ge m-r'\), not the reverse.  Substitution in (13) gives (5).
- If \(\ell>n\), (5) gives exponent zero; if \(\ell=n\) is prime, it gives
  \(1+0-1=0\).  For \(\sqrt n<\ell<n\), both floor logarithms are one, so
  the exponent is at most two.  For \(\ell\le\sqrt n\), the weaker bound
  \(v_\ell(E_n)\le2\lfloor\log_\ell n\rfloor\) yields (16).  Summing over
  at most \(\sqrt n\) integers is a valid deliberately crude estimate; no
  prime number theorem enters here.

### Frobenius/Lucas step: (17)--(19)

In \(\mathbb F_\ell[[x]]\), with \(D=1-2x-x^2\), set
\(H=D^{(\ell-1)/2}F(x^\ell)\).  Frobenius gives
\(D(x^\ell)=D(x)^\ell\), hence \(H^2=D^{-1}=F^2\).  Both series have
constant term one.  Since \(H+F\) has nonzero constant term two, it is a
unit, so \((H-F)(H+F)=0\) implies \(H=F\).  This supplies the uniqueness
detail implicit in (17).

The polynomial \(D^{(\ell-1)/2}\) has degree exactly \(\ell-1\).  Its
coefficient at \(d<\ell\) is \(U_d\), and coefficient comparison at
\(c\ell+d\) proves (18) for every \(c\ge0\), \(0\le d<\ell\).  The leading
coefficient is \((-1)^{(\ell-1)/2}\), proving the nonzero statement (19).

This derivation is self-contained, but the result is not new.  Noe defines
\(T_n\) as the coefficient of \(x^n\) in \((a+bx+cx^2)^n\), with

\[
T_n=\sum_k {2k\choose k}{n\choose2k}b^{n-2k}(ac)^k.
\]

At \((a,b,c)=(1,2,2)\), this is \(T_n=2^nU_n\).  Noe's equation (13) is
the full base-\(\ell\) digit product for \(T_n\).  Fermat's theorem gives
\(2^{c\ell+d}\equiv2^{c+d}\pmod\ell\), so it translates exactly to the
iterated (18).  Noe's equation (14), with discriminant \(-4\) and \(k=0\),
also yields (19).  Thus the correct status is rediscovery.

### Large-prime survivor calculation and exact iff: (20)--(28)

For \(\sqrt n<\ell<n\), division gives uniquely
\(n=a\ell+s\) with \(1\le a<\ell\) and \(0\le s<\ell\).  Also
\(n<\ell^2\), so no denominator \(j+1\le n\) in (20) contains \(\ell^2\).
After multiplication by \(\ell\), precisely the denominators
\(j+1=c\ell\), \(1\le c\le a\), survive modulo \(\ell\).  Their paired
indices are exactly (21), and \(\ell/(j+1)=1/c\) in \(\mathbb F_\ell\).
Applying (18) twice gives

\[
\ell V_n\equiv U_sU_{\ell-1}
 \sum_{c=1}^a U_{a-c}U_{c-1}/c
=U_sU_{\ell-1}V_a\pmod\ell,
\]

so (22) has no omitted survivor or denominator problem.

Here \(v_\ell(V_n)\ge-1\).  Equation (13) with \(r=1\) and
\(v_\ell(U_n)\ge0\) gives

\[
v_\ell(E_n)\ge1\iff v_\ell(V_n)\ge0
\iff \ell V_n\equiv0\pmod\ell.
\]

Because (19) is a unit and a field has no zero divisors, (22) proves the
exact iff (7), not merely one implication.  Since \(a,s<\ell\), multiplying
by \(a!\) or \(s!\) is invertible, so (24) and (25) are exactly equivalent.
The exponent-two witnesses and the \(P_3=19\) full block were replayed with
the independently reconstructed integer \(E_n\).

### Added numerator-branch cutoff: (28a)--(28e)

For fixed \(n\), each eligible prime has the unique
\(a=\lfloor n/\ell\rfloor\), equivalent to the half-open interval (28a).
If it lies in the \(V_a\) branch, it divides \(P_a\) because \(a<\ell\).
Thus the sum of logarithms of the distinct such primes is at most
\(\log P_a\).  Positivity of the recurrence and, for example,
\(P_a\le Q_a\) with the explicit formula for \(Q_a\), supplies the more
than sufficient bound \(\log P_a=O(a\log(a+2))\).

For \(A=\lfloor n^{1/3}\rfloor\), summing this bound over \(a\le A\) is
\(O(A^2\log A)=o(n)\).  When \(a>A\), (28a) implies \(\ell<n/A\).  Ignoring
both primality and divisibility leaves at most \(n/A\) positive integers,
each with logarithm at most \(\log n\), giving (28d).  The branches may
overlap, but only an upper bound is asserted, so overlap causes no error.
This proves (28e).

### Zero-set decomposition and equivalence: (29)--(34)

The odd prime factors \(\ell\ge n\) contribute zero by (5); the total
contribution from \(\ell\le\sqrt n\) is a nonnegative \(o(n)\) term by
(16).  The remaining factors are exactly \(\mathcal Z_n\) by (7), each
with exponent one or two.  Therefore (30)--(32) follow (with the occurrences
of \(o(n)\) denoting possibly different error functions).

For (33), if \(W_n=o(n)\), the upper inequality gives
\(\log\operatorname{odd}(E_n)=o(n)\).  Conversely the exact decomposition
has nonnegative small-prime contribution and exponent at least one on every
\(\ell\in\mathcal Z_n\), so
\(W_n\le\log\operatorname{odd}(E_n)\); hence an \(o(n)\) logarithm forces
\(W_n=o(n)\).  This verifies both directions without subtracting an
uncontrolled signed error.

Equation (28e) further shows that the union zero set is subexponential iff
the \(U\)-branch (33a) is; overlap again changes neither implication.  By
(18), a prime in that branch divides \(U_n\).  The product of distinct such
primes divides the reduced numerator of \(U_n\).  Formula (11) supplies a
common denominator \(2^{\lfloor n/2\rfloor}\), and the coefficient
asymptotic from (9) gives (33c).  Its constant is positive and insufficient,
as the report says.  Finally (34) is the immediate crude bound together with
the prime-number-theorem form \(\vartheta(n)=n+o(n)\).

The separate two-adic observation (35) remains only a `conjecture` backed by
an `experiment`; it is not used above.

## Independent computation

The independent checker shares no code with the primary checker.  It:

- reconstructs \(P_n,Q_n,E_n\) and verifies integrality of (4);
- checks (3), (10)--(15) with exact `Fraction` arithmetic;
- constructs \(D(x)^{(\ell-1)/2}\) directly and checks (17)--(19);
- verifies \(T_n(1,2,2)=2^nU_n\);
- checks the survivor identity (22), both directions of (7), and (24)--(25)
  for all 118,613 strict pairs \(\sqrt n<\ell<n\) through \(n=1200\), of
  which 1,468 are exceptional;
- checks the odd-prime product decomposition through 799 depths, including
  overlapping \(U\)- and \(V\)-branch products and (33c)'s divisibility.

Exact output:

```text
PASS: independent exact replay of (3)-(32), including strict (7), on 118613 large-prime pairs (1468 exceptional) and product decompositions at 799 depths
LITERATURE MAP: T_n(1,2,2)=2^n U_n, so Noe (2006), equation (13), already contains the Lucas product; no novelty or V1 claim
```

The primary checker, after the strict-boundary correction, prints:

```text
PASS: normalized determinant/exponent bound, Lucas product, and exact large-prime zero criterion on 84219 pairs (1197 exceptional), including exponent-two and V_a-block witnesses
EXPERIMENT: v_2(Q_n)-floor(n/2) follows the stated mod-4 pattern through n=10000; no all-n proof is claimed
```

## Primary-source and mathlib record

- Tony D. Noe,
  [*On the Divisibility of Generalized Central Trinomial Coefficients*,
  Journal of Integer Sequences 9 (2006), Article 06.2.7](https://cs.uwaterloo.ca/journals/JIS/VOL9/Noe/noe35.pdf).
  Checked equations (1)--(2), (11)--(14), and Theorem 8.6 in the official
  PDF.  Official PDF SHA-256:
  `971d271f35eb4400ac223f7e3536cdc7ac28e14393caa03c1204bc16d30a094c`.
- Eric Rowland and Reem Yassawi,
  [*Automatic congruences for diagonals of rational functions*](https://arxiv.org/abs/1310.8635),
  and Boris Adamczewski and Jason P. Bell,
  [*On vanishing coefficients of algebraic power series over fields of
  positive characteristic*](https://arxiv.org/abs/1205.4091), concern fixed
  characteristic and do not supply the varying-prime estimate (33b).
- The local mathlib search reconfirmed Lucas's theorem in
  `Mathlib/Data/Nat/Choose/Lucas.lean` and shifted Legendre infrastructure in
  `Mathlib/RingTheory/Polynomial/ShiftedLegendre.lean`; it found no direct
  theorem closing the remaining varying-prime estimate.

Absence from this bounded search is not a novelty claim.  In particular, the
audit positively found and recorded prior art for the Lucas component.

## Reproduction and pins

Run:

```bash
python work/ultrapi-resume/gauss_exceptional_gcd_upper_bound_check.py
python work/ultrapi-resume/gauss_exceptional_gcd_upper_bound_independent_check.py
```

The final SHA-256 pins are recorded after the final frozen rerun below:

- corrected primary report:
  `f2b248e80f9e053362402b1865b7fae8763f6a999061a8cba1c021f7ec7170ad`
- corrected primary checker:
  `6579baf3d9f77f382b7b765ef055ce077e427221674f640381a8157a2a656ec1`
- independent checker:
  `ac07f1c36f9c336bdb3427d1aaea7b6c06e2f2cb83546aca83c3c2b2f8e5fb83`
- this audit: compute the file SHA-256 with the literal token
  `INDEPENDENT_AUDIT_SHA256` in this line

The audit-file pin is necessarily computed over the final file with the
`INDEPENDENT_AUDIT_SHA256` token left literal, avoiding a self-hash paradox.

## Handoff

The proved reduction is materially sharper after (28e): the full
earlier-numerator \(V_a\) branch is already \(o(n)\), leaving the
earlier-denominator set (33a) as the only odd-primary exponential-scale
obstruction.  The fixed-numerator bound (33c) is too weak to establish that
obstruction's \(o(n)\) estimate.  The two-adic edge is also unproved.  This is
meaningful route progress, but no complete proof about all finite decimal
words in pi.
