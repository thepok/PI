# Independent audit: simultaneous Hutton primary phases

Audit date: **2026-08-12 UTC**  
Audited report:
[hutton_primary_phase_attack.md](hutton_primary_phase_attack.md)  
Primary checker:
[hutton_primary_phase_check.py](hutton_primary_phase_check.py)  
Independent checker:
[hutton_primary_phase_independent_check.py](hutton_primary_phase_independent_check.py)

Audited artifact SHA-256 values:

- report:
  \(f8a5757b142cc888ea5db84c4e1955744ac373bd8f3b756a8e4599757f3fb74c\);
- primary checker:
  \(fff42fb9cee07b5f488f8a7daf2c090e105e0f6462d2c2ab8a402ba0251977bc\);
- independent checker:
  \(4a5e56c4799cbfce132a229601700b66be94e07eb21395a62c53bd114c9c48af\).

## Verdict

**PASS at the proof sketch label, after the corrections recorded below.**

The infinite-family valuation formulas, leading-unit formulas, high-prime
enrichment, subexponential complementary-modulus bound, exact
selected/complementary phase identity, and stationary-lift obstruction all
survived independent rederivation. The finite replay is correctly labeled an
experiment. These results are not Lean declarations, so this audit does not
upgrade them to machine-checked. They do not prove a decimal cylinder hit for
pi: canonical V1 remains a conjecture.

No fatal mathematical gap was found. The report originally needed four
precision repairs:

1. the \(t\ge u\) branch of the dominant-layer proof now explicitly records
   \(t\le\lfloor\log_pR\rfloor\), and the cross-base terms in both leading-unit
   congruences are explicitly bounded;
2. the actual one-prime additive coordinate for every surviving high prime is
   now displayed and checked, rather than being left implicit behind the
   singular-prefix residue;
3. the primary decimal period is now given by an explicit formula and checked
   for exact minimality in the independent replay; and
4. the original count 1,429,290 mixed 1,429,278 enumerated scores with 12
   maximum assertions. The report and checker now expose those counts
   separately.

The broad statement about shallow primary information was also narrowed to
the precise least-CRT-lift construction used by the chord argument. The
Untrau source is now versioned and byte-hashed.

## 1. Source and statement audit

The canonical source is problems/local/pi-digits.txt, SHA-256

\[
\texttt{2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825}.
\]

It is Marcel's immutable local question and supplies no external source URL;
the report correctly invents none. Its V1 normalization quantifies over every
finite padded decimal word and asks for one contiguous occurrence. The report
keeps the three relevant quantifiers separate: the exact arithmetic family,
the number of complementary residues, and the one numerator actually selected
by the Hutton rational. In particular it does not replace the last pointwise
quantifier by an average.

## 2. Dominant-layer lemma

Let \(d=R-r>0\) and \(t=v_p(r)\). Because \(R,r\) are odd, \(d\) is even.

- If \(t<u=v_p(R)\), then \(p^t\mid d\). For \(t=0\), parity gives
  \(d\ge2=t+2\). For \(t\ge1\), \(d\ge p^t\ge t+2\) for every odd prime.
- If \(t\ge u\), then \(p^u\mid d\). Also \(p^t\le r<R\), hence
  \(t\le\lfloor\log_pR\rfloor\). The hypothesis gives
  \(d\ge p^u\ge\lfloor\log_pR\rfloor+2\ge t+2\).

Thus \(t\le d-2\), equivalently \(r+v_p(r)\le R-2\). This closes the branch
that was easiest to misread.

For \(R_a=3^a7^{a+1}\), \(a\ge2\), the report's elementary estimates are
valid:

\[
\lfloor\log_3R_a\rfloor\le3a+1\le3^a-2,\qquad
\lfloor\log_7R_a\rfloor\le2a\le7^{a+1}-2.
\]

The parity calculation also gives \(R_a\equiv3\pmod4\). The independent
checker tested 629 additional small lemma instances, covering 369,217 odd
scores, and separately reproduced the family counts.

## 3. Unique minima and leading units

At 3, a base-3 term has valuation \(-r-v_3(r)\). All earlier such terms have
valuation at least \(-(R_a-2)\), whereas the final term has valuation
\(-(R_a+a)\). A base-7 term has valuation \(-v_3(r)\), so it cannot tie the
final base-3 term. The minimum is unique. Interchanging 3 and 7 gives

\[
v_3(H_{K_a})=-(R_a+a),\qquad
v_7(H_{K_a})=-(R_a+a+1).
\]

Reduction of \(H_{K_a}=P_a/Q_a\) therefore gives exactly the two denominator
exponents claimed in the report.

After scaling at 3, every preceding base-3 term has valuation at least
\(a+2\), and every cross-base term has valuation
\(R_a+a-v_3(r)\ge a+2\). The surviving final unit is
\(-8\,7^{-(a+1)}\). The symmetric 7-adic calculation has cross-base
valuation \(R_a+a+1-v_7(r)\ge a+3\) and surviving final unit
\(-4\,3^{-a}\). Hence the two rational congruences (17)--(18) are valid.

For the post-transient state
\(A_a\equiv2^{b_a}P_a\pmod {m_a}\), additive-CRT recombination multiplies the
3-local unit by \(10^{b_a}7^{R_a+a+1}\), and the factor \(7^{a+1}\)
cancels the unit denominator. This gives

\[
\xi_a\equiv-8\,10^{b_a}7^{R_a}\pmod {3^{a+2}}.
\]

The same computation gives
\(\xi_a\equiv-4\,10^{b_a}3^{R_a}\pmod {7^{a+3}}\). Thus the report is using
the actual additive coordinate, not the unreduced numerator.

## 4. High primes and the complementary modulus

Every summand denominator divides

\[
3^R7^R\operatorname{lcm}\{1,3,5,\ldots,R\}.
\]

Consequently a prime \(p>\sqrt R\) can occur in \(Q_a\) with exponent at most
one. For \(p>7\), \(p\le R<p^2\), multiplication by \(p\) kills every
nonsingular summand modulo \(p\). Writing the singular indices as \(cp\),
Fermat's theorem and multiplicativity of \(\chi_4\) give exactly

\[
pH_K\equiv\chi_4(p)A_n\pmod p.
\]

Therefore \(p\) survives precisely when this residue is nonzero. If it
survives, its actual post-transient additive coordinate is

\[
\gamma_{a,p}\equiv A_a(m_a/p)^{-1}
\equiv10^{b_a}\chi_4(p)A_n\pmod p.
\]

The primary checker and independent checker both compare this formula with
the coordinate reconstructed from the fully reduced rational.

After removing the exact full 3- and 7-primary powers, \(5^{b_a}\), and all
surviving primes above \(\sqrt {R_a}\), each prime power in \(D_a\) is at
most \(p^{\lfloor\log_pR_a\rfloor}\le R_a\), with
\(p\le\sqrt {R_a}\). Hence

\[
D_a\le\prod_{p\le\sqrt {R_a}}R_a
\le R_a^{\sqrt {R_a}}=\exp(o(R_a)).
\]

The factors removed from \(m_a\) have disjoint prime support, so
\((F_a,D_a)=1\). No unaccounted factor 2 remains because T66 proves the
reduced Hutton denominator odd.

## 5. Exact phase identity and stationary separator

For \(m_a=F_aD_a\), the definitions

\[
\alpha_a\equiv A_aD_a^{-1}\pmod {F_a},\qquad
\beta_a\equiv A_aF_a^{-1}\pmod {D_a}
\]

are the two additive-CRT coordinates. Their embedded numerators sum to
\(A_a\) modulo \(m_a\), proving

\[
e_{F_a}(\alpha_a10^s)e_{D_a}(\beta_a10^s)
=e_{m_a}(A_a10^s)=e(10^{b_a+s}H_{K_a}).
\]

Thus the selected and complementary phases are correlated exactly as the
report says.

The least CRT lift \(\widetilde\xi_a\) of the two shallow primary residues is
a unit at 3 and 7. Both \(\widetilde\xi_a/F_{0,a}\) and the actual primary
coordinate therefore have reduced denominator \(F_{0,a}\). LTE gives

\[
\operatorname{ord}_{3^E}(10)=3^{E-2},\qquad
\operatorname{ord}_{7^G}(10)=6\,7^{G-1},
\]

and CRT gives the exact common decimal period

\[
\operatorname{ord}_{F_{0,a}}(10)
=2\,3^{R_a+a-2}7^{R_a+a}.
\]

For the \(a=2\) sample, the independent checker verifies
\(10^T\equiv1\pmod {F_{0,a}}\) for this \(T\), and verifies noncongruence
after dividing \(T\) by each of its possible prime divisors \(2,3,7\).
That proves exact minimality rather than merely testing one period candidate.

Finally,

\[
\left|\frac1N\sum_{s<N}e_{F_{0,a}}(\widetilde\xi_a10^s)-1\right|
\le\frac{2\pi\widetilde\xi_a(10^N-1)}{9NF_{0,a}}
<\frac{2\pi M_a(10^N-1)}{9NF_{0,a}},
\]

which yields the report's lower bound for the mean magnitude. Since
\(\log M_a=O(a)\) and
\(\log F_{0,a}=R_a\log21+O(a)\), it tends to one throughout every fixed
range \(N\le(\log_{10}21-\delta)R_a\) when
\(0<\delta<\log_{10}7\). This strictly contains the
\(R_a\log_{10}3+O(\log R_a)\) Hutton transfer scale.

## 6. Exact replay

The corrected primary checker reports:

- 95 family bound checks;
- 1,429,278 explicitly enumerated earlier scores and 12 maximum assertions;
- 425 high primes in the \(a=2\) sample, 1,275 classification assertions,
  and 425 checks of the actual one-prime coordinate;
- exact denominator exponents \(v_3(Q)=3089\), \(v_7(Q)=3090\),
  \(v_5(Q)=4\);
- the exact 37-digit complement
  \(3443846140271004739007417826008487767\);
- 1,473 transferable post-transient offsets; and
- a stationary-lift chord error smaller than \(10^{-2609}\).

The independent checker reproduces these invariants through a separately
written implementation, verifies the source and literature hashes, tests the
dominant lemma on additional radii, and checks exact period minimality by
modular exponentiation. Its retained output is:

    claim_status=experiment
    source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
    dominant_lemma_instances=629
    dominant_lemma_score_checks=369217
    family_assertions=95
    enumerated_family_scores=1429278
    maximum_assertions=12
    high_primes=425
    surviving_high_primes=425
    actual_high_prime_coordinate_checks=425
    exact_period_digits=4084
    stationary_lift=1091638
    horizon=1476,offsets=1473
    all independent exact checks passed

The complex phase means in the primary checker use floating-point
evaluation and remain an experiment only. None is used to justify an
asymptotic claim.

## 7. Literature and formal-status audit

The following local source pins were rehashed:

- Kerr PDF:
  \(9136dc3965da376942f653b2b06de8d92d7e5e997ee536e1257979698b73e4bd\);
- Konyagin--Shparlinski PDF:
  \(46f7981327913a4a7adbca724a7b3a214520ed6a946b46baba80ba8af55d97bc\).

The pinned Kerr theorem indeed treats a prime modulus and gives the first
branch \(p^{1/8}N^{71/96+o(1)}\), nontrivial only beyond
\(N>p^{12/25+o(1)}\). The pinned Konyagin--Shparlinski interval-gap result is
for primitive roots in a prime field and is developed for
\(p^{1/2}<N<p\). Untrau version 1 was freshly fetched from arXiv and
byte-hashed as

\[
\texttt{edf36a7a2cc19f8787006cf8656bc218796cc887f3cf100087a5c71ded8cfc5f}.
\]

Its abstract and definitions study families of complete sums indexed by a
subgroup of fixed order as prime-power moduli vary. It does not supply the
pointwise logarithmic-length ordered-prefix estimate required here. The
bounded applicability statements are therefore literature-checked.

No file under ErdosLab or TheoryLib was changed by this branch. None of the
new claims is registered in audit/AxiomAudit.lean, and no machine-checked
status is asserted. Formalization would still require named lemmas for the
dominant layer, exact valuations, scaled units and CRT transport, and the
small-prime complement bound.

## Terminal assessment

The audited arithmetic package is valid at proof sketch level. It gives
strong simultaneous primary control and determines all but an
\(\exp(o(R_a))\) complement, but it does not steer the one actual phase. The
stationary lift proves that the displayed \(O(a)\)-depth primary data and
exact period alone cannot yield a uniform short-sum theorem. Supplying the
complete actual coordinate restores the exact fixed-pi phase identity, not
independence. No cylinder hit, candidate resolution, or verified resolution
follows.
