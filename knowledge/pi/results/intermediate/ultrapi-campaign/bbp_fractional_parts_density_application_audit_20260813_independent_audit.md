# Independent audit: BBP fractional-parts density applicability

Audit date: **2026-08-13 UTC**

Primary artifact:
[bbp_fractional_parts_density_application_audit_20260813.md](bbp_fractional_parts_density_application_audit_20260813.md),
SHA-256
`55383eb4a52f65373c841dd86fdc5bf939d96e5a8ad536bae4a03e43de71135d`.
Its companion checker was pinned but treated as untrusted and never imported:
[bbp_fractional_parts_density_application_audit_20260813_check.py](bbp_fractional_parts_density_application_audit_20260813_check.py),
SHA-256
`8c43ce5a7739337fd3273b6a612879ae68d302b7bbc5b18ba0b5aea8ad4f4885`.

Frozen upstream input:
[bbp_dyadic_diagonal_functional_recurrence_20260813.md](bbp_dyadic_diagonal_functional_recurrence_20260813.md),
SHA-256
`8768abbdd38d21721955f76a0c1ba90054ed9177a95b9b393aa393fc0d7466ba`.

## Outcome

**No fatal gap was found in the corrected artifact's claimed scope.**  In
particular, the seventh-slot Bézout recombination really removes the apparent
half-integral obstruction and leaves 28 two-integral terms with odd affine
denominators.  All 28 lift signs, including both non-obvious
\(+\tfrac12\) signs, are correct.  The prime-binomial and complementary-
cofactor formulas and the van-der-Corput recurrence separator also survive
independent derivation.

The algebraic identities and logical separator retain status `proof sketch`,
the independently retrieved source audit is `literature-checked`, and the
bounded replay is an `experiment`.  No cited scalar theorem applies to the
full synchronized BBP forcing or state.  Canonical V1 remains a `conjecture`;
nothing here is `machine-checked`, a `candidate resolution`, or a
`verified resolution`.

The first genuinely missing implication is the same one stated in the
primary artifact: no theorem controls the selected roots jointly across the
28 affine moduli and then propagates that control through the state-dependent
decimal recurrence.  Because the artifact explicitly denies that
implication, this is a research barrier rather than a gap in its argument.

## 1. Four poles and the seventh-slot recombination

Independent cross-multiplication confirms

\[
 a(k)=\frac4{8k+1}-\frac1{2(2k+1)}
      -\frac1{8k+5}-\frac1{2(4k+3)}.              \tag{IA1}
\]

At slots \(j\le6\), the factor
\(s=5^{n+1}16^{7-j}\) supplies enough powers of two to make each
numerator in (IA1) integral.  At \(j=7\), \(s=5^{n+1}\) is odd and the
second and fourth terms are separately non-two-integral.

Let

\[
 A=2k+1,\qquad B=4k+3=2A+1.
\]

Then the two problematic terms first combine as

\[
 -\frac{s}{2A}-\frac{s}{2B}
 =-\frac{s(3k+2)}{AB}.                              \tag{IA2}
\]

The stronger linear recombination is exact:

\[
 -\frac{s(k+1)}A+\frac{s(2k+1)}B
 =\frac{s\bigl(A^2-(k+1)B\bigr)}{AB}
 =-\frac{s(3k+2)}{AB},                              \tag{IA3}
\]

because

\[
 (2k+1)^2-(k+1)(4k+3)=-(3k+2).
\]

Thus the corrected endpoint is genuinely 28 indexed odd-linear terms, not
26 linear terms plus one unavoidable quadratic term.  The numerators in the
two recombined fractions depend on \(k\), but their residues simplify to
fixed rational phase coefficients, as checked next.

## 2. All lift signs and exact reconstruction

For any recombined term \(u/L\), with \(L\) odd, put

\[
 \rho\equiv uL^{-1}\pmod M,\qquad
 H=\frac{L\rho-u}{M},\qquad M=2^{27(n+1)}.
\]

Then

\[
 \frac\rho M=\frac HL+\frac{u}{LM},\qquad
 H\equiv-uM^{-1}\pmod L.                           \tag{IA4}
\]

Writing \(R=5\,2^{-27}\), \(e_j=4(7-j)\), and
\(s=5^{n+1}2^{e_j}\), one has

\[
                         sM^{-1}=2^{e_j}R^{n+1}.     \tag{IA5}
\]

Equations (IA4)--(IA5) independently give the phase coefficients, in pole
order \((8k+1,2k+1,8k+5,4k+3)\),

\[
 \begin{cases}
 (-4\,2^{e_j},\ +2^{e_j-1},\ +2^{e_j},\ +2^{e_j-1}),
       &1\le j\le6,\\[2mm]
 (-4,\ +\tfrac12,\ +1,\ +\tfrac12),&j=7.
 \end{cases}                                       \tag{IA6}
\]

The two delicate signs in the second row follow without numerical
guesswork:

- for \(L=A=2k+1\), \(2(k+1)=A+1\), so
  \(k+1\equiv\tfrac12\pmod A\);
- for \(L=B=4k+3=2A+1\), \(-2A\equiv1\pmod B\), so
  \(-A\equiv\tfrac12\pmod B\).

The fourth recombined numerator is \(+sA\), and the leading minus sign in
\(H\equiv-uM^{-1}\) is what changes \(A\) to \(-A\); hence the second
\(+\tfrac12\) in (IA6) is correct.

Reduction modulo \(M\) is additive in the ring of two-integral rationals.
Summing (IA4) over all 28 pieces therefore gives exactly

\[
 \Gamma_n=\left\{\sum_{t=1}^{28}\frac{H_t}{L_t}
                         +\frac{b_n}{M_n}\right\}.  \tag{IA7}
\]

The independent checker verifies (IA7), all 28 signs, and the two bad formal
terms at every depth \(0\le n\le96\).  Including \(n=0\) extends the primary
checker's positive-depth scan and exposes no endpoint exception.

The 28 affine functions are distinct as functions of \(n\).  Exactly four
have a fixed divisor:

\[
 28n+7,\quad56n+21,\quad14n+7,\quad56n+49,
\]

each with fixed divisor seven.  This independently confirms the obstruction
to requiring all 28 denominators to be prime.

## 3. Original quartic factors and CRT

For

\[
 A=2k+1,\quad B=4k+3,\quad C=8k+1,\quad D=8k+5,
\]

Euclidean reduction gives exactly

\[
 \begin{array}{c|cccccc}
 \text{pair}&(A,B)&(A,C)&(A,D)&(B,C)&(B,D)&(C,D)\\ \hline
 \gcd&1&\gcd(A,3)&1&\gcd(B,5)&1&1.
 \end{array}                                       \tag{IA8}
\]

For each fixed slot \(k=7n+j\), the residue classes producing the common
factor three or five occur infinitely often because seven is invertible
modulo both three and five.  Hence there is no uniform four-factor CRT.

Even in a pairwise-coprime instance, CRT reconstructs

\[
 \frac hd\equiv\sum_r
 \frac{h_r\, (d/L_r)^{-1}\bmod L_r}{L_r}\pmod1,    \tag{IA9}
\]

so the coefficient of the \(r\)-th local residue depends on the complementary
factors.  This does not instantiate a collection of independent fixed-base
scalar sequences.

## 4. Prime and composite binomials

Each height in (IA7) has

\[
 H_n\equiv C R^{n+1}\pmod{L(n)},\qquad
 L(n)=An+B,qquad A\in\{14,28,56\},                 \tag{IA10}
\]

with fixed signed dyadic \(C\).  If \(p=L(n)\) is prime and
\(p\nmid10C\), then

\[
 \begin{aligned}
 H_n^A
 &\equiv C^A R^{A(n+1)}
  =C^A R^{p+A-B}\\
 &\equiv C^A R^{A-B+1}\pmod p.                    \tag{IA11}
 \end{aligned}
\]

The final exponent contains the essential \(+1\), and the primary artifact
has it correctly.  Equation (IA11) makes \(H_n\) one distinguished root of
a fixed binomial; it does not average all roots.

If \(L(n)=pq\) is composite and \(p\) is a prime divisor, then

\[
 A(n+1)=pq+A-B.
\]

For \(p\ne5\), Fermat reduces \(pq\) to \(q\) in the exponent and gives

\[
 H_n^A\equiv C^A R^{q+A-B}\pmod p.                 \tag{IA12}
\]

Thus the local right side contains the complementary cofactor \(q=L/p\).
The independent scan found 6,872 pairs consisting of a fixed affine form and
a fixed prime for which this target takes at least two different values as
the cofactor changes.

There is one harmless qualification to the wording “the same calculation.”
When \(p=5\), \(R\equiv0\pmod5\), so Fermat's unit calculation is unavailable.
For all 28 forms the exponent \(q+A-B\) is nevertheless positive whenever
five divides the composite modulus.  Indeed, checking the least nonnegative
solution \(n\pmod5\) for each of the 28 fixed affine forms gives minimum
exponent two, and replacing \(n\) by \(n+5\) increases \(q\) by \(A\).
Thus (IA12) holds directly as \(0=0\).
The independent checker separates and verifies these cases.  The formula is
correct, but its \(p=5\) proof is not literally the Fermat calculation.

The fixed-integer-base obstruction is also exact.  If one integer \(a\)
represented \(R\) modulo infinitely many unbounded \(L(n)\), every such
modulus would divide the fixed integer \(2^{27}a-5\).  Hence that integer
would be zero, which is impossible for integral \(a\).  A varying rational
modular base therefore cannot be silently replaced by the fixed integer base
required in the cited density theorems.

## 5. Independent source audit

All five PDFs were independently downloaded again from the primary links on
2026-08-13 UTC.  Their bytes match the primary artifact's pins:

| source | independently verified scope | SHA-256 |
|---|---|---|
| Cilleruelo--Kumchev--Luca--Rué--Shparlinski, [*On the Fractional Parts of \(a^n/n\)*](https://upcommons.upc.edu/bitstreams/ae5e82a0-9bb2-4dd3-8dbc-b22da011adf5/download) | Theorem 1 uses the explicit semiprime set \(\{pq:q\le\log p/\log a\}\) for a fixed integer \(a\ge2\). Theorem 2 covers every interval of length at least \(cN^{-0.475}\) with some literal \(\{a^n/n\}\), \(n\le N\). Its proof uses \(p\equiv1\pmod{q-1}\) to reduce \(a^{pq}/(pq)\) to \(a^q/(pq)\). | `e5ab04087aa7f162b9431a003c16ccba9558d32f5e088ec7565bf6d6c2154164` |
| Dubickas, [*Density of some sequences modulo 1*](https://www.impan.pl/shop/en/publication/transaction/download/product/87011) | Theorem 1.2 treats \(Q(\alpha^n)/n\) for Pisot or Salem \(\alpha\). Replacing \(n\) by a polynomial \(P(n)\) of degree at least two is explicitly proposed as a future extension. | `9b16c0a16187f9a9e75475e25abbf9c11c7f79b69ebafe340d7762ca60f0bf0e` |
| Dubickas, [*Density of Some Special Sequences Modulo 1*](https://epublications.vu.lt/object/elaba%3A164926835/164926835.pdf) | Theorem 2 has fixed integer \(a\), literal denominator \(n^d\), and hypothesis \(\operatorname{rad}(d)\mid\operatorname{rad}(a)\). It does not cover a product of distinct affine factors or the modular rational base \(R\). | `74bc3bdd4b05d6ebff3935f1dc4cddca37990fc6288a90946a2449ebc21149cd` |
| Lind, [arXiv:2308.14354v2](https://arxiv.org/pdf/2308.14354v2) | Theorem 1 fixes a prime \(q>b^2\) and finds the limit points of \(b^{qp}\bmod(qp)\) as the prime \(p\) varies. Exponent and modulus remain tied to the same product \(qp\). | `d02adcb8aeb29fb5ac9e6d4be79ebb81728aef939e04e3f8ebd80f3959f5156e` |
| Kowalski--Soundararajan, [arXiv:2003.12965v2](https://arxiv.org/pdf/2003.12965v2) | Fixed sets \(A_{p^v}\) are combined by CRT and the probability measure is uniform over all elements of the resulting \(A_q\). A singleton fibre has discrepancy one. The introduction identifies higher-degree root distribution over primes as outstanding beyond the established quadratic case. | `82bf98763cd587fd77c07df08ff4583623a9a9b7b9d5b0a0fc2f9e76d425b809` |

The source verdict in the primary artifact is therefore accurate.  None of
these theorems supplies a selected-root estimate for (IA10), a uniform local
set independent of the complementary cofactor in (IA12), a joint theorem for
all 28 coordinates, or a state-conditional estimate.

## 6. Van-der-Corput separator

Let \(r_k\) be the base-two van der Corput sequence and define

\[
 Y_{2k}=0,\quad Y_{2k+1}=r_k/10,\qquad
 \Delta_{2k}=r_k/10,\quad\Delta_{2k+1}=\{-r_k\}.
\]

Then

\[
 \{10Y_{2k}+\Delta_{2k}\}=r_k/10=Y_{2k+1}
\]

and

\[
 \{10Y_{2k+1}+\Delta_{2k+1}\}
 =\{r_k+\{-r_k\}\}=0=Y_{2k+2}.                    \tag{IA13}
\]

Every state remains in \([0,1/10)\), so a fixed interval such as
\([1/5,3/10]\) is never hit.  Meanwhile the odd forcing subsequence is the
reflected van der Corput sequence and is uniformly distributed.

The coverage-rate statement is also exact.  Among the first \(N\) forcing
terms there are \(K=\lfloor N/2\rfloor\) odd terms.  If \(2^m\le K<2^{m+1}\),
the first \(2^m\) odd terms form a reflected complete grid of circular mesh
\(2^{-m}\).  Since \(2K+1<4\cdot2^m\), this mesh is less than \(4/N\).
For every fixed \(c>0\), eventually

\[
 4/N<cN^{-0.475}.
\]

Thus the model has both an equidistributed forcing subsequence and stronger
shrinking-interval coverage than the cited \(N^{-0.475}\) scale, while its
state avoids a fixed target.  This is a valid logical separator and, as the
primary artifact stresses, not a model of the actual BBP correlations.

## 7. Independent checker

The independent checker is
[bbp_fractional_parts_density_application_audit_20260813_independent_check.py](bbp_fractional_parts_density_application_audit_20260813_independent_check.py),
SHA-256
`55d105e2933bc6e9cfddd4b8416c2ab61577b5f4b33cfc079ec1725bd10097be`.
It uses only the Python standard library, imports no branch checker, and
performs separate prime and \(p=5\) composite checks.

Run from the repository root:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_fractional_parts_density_application_audit_20260813_independent_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_fractional_parts_density_application_audit_20260813_independent_check.py
```

Retained result:

```text
status: PASS_INDEPENDENT_NO_FATAL_GAP_NO_APPLICATION_BRIDGE
bounded_replay_label: experiment
algebraic_claim_label: proof sketch
literature_audit_label: literature-checked
partial_fraction_checks: 513
bezout_symbolic_checks: 1
bezout_instance_checks: 1024
exact_depth_range_including_zero: [0, 96]
exact_split_checks: 97
half_integral_formal_terms_per_depth: 2
exact_lift_checks: 2716
exact_sign_checks: 2716
formal_affine_forms: 28
odd_linear_terms_after_recombination: 28
coupled_quadratic_terms_after_recombination: 0
gcd_table_checks: 2001
prime_binomial_checks: 13680
composite_binomial_checks_away_from_five: 127203
composite_binomial_direct_five_checks: 14000
cofactor_variation_witness_count: 6872
van_der_corput_grid_checks: 14
van_der_corput_mesh_bound_checks: 9998
recurrence_transition_checks: 8192
asserts_scalar_density_theorem_applies: false
asserts_forcing_discrepancy: false
asserts_state_target_hitting: false
asserts_v1: false
```

The corrected primary artifact therefore passes independent audit at its
stated boundary: an exact 28-linear working stone and a
`literature-checked` non-applicability result, not a proof that any prescribed
decimal word occurs in pi.
