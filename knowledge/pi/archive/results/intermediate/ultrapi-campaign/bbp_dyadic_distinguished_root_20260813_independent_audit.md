# Independent audit: BBP dyadic distinguished-root reduction

Audit date: **2026-08-13 UTC**

Primary artifact audited:
[bbp_dyadic_distinguished_root_20260813.md](bbp_dyadic_distinguished_root_20260813.md),
SHA-256
`d70f8cd56885e77aecdec9eb09f67575d2b8ffe4e972d66ff9a69d82386466b8`.
Its checker was treated as untrusted and was not imported:
[bbp_dyadic_distinguished_root_20260813_check.py](bbp_dyadic_distinguished_root_20260813_check.py),
SHA-256
`e7103ffab23b88fb5bdf83fab73bcc1979f2ce3075dce2740d074d65f3b2b304`.

The frozen upstream recurrence report was also pinned:
[bbp_dyadic_diagonal_functional_recurrence_20260813.md](bbp_dyadic_diagonal_functional_recurrence_20260813.md),
SHA-256
`8768abbdd38d21721955f76a0c1ba90054ed9177a95b9b393aa393fc0d7466ba`.

## Outcome

**No fatal gap was found within the artifact's stated scope.**  The exact
28-term reduction, the safe treatment of the half coefficients, the
distinguished-root congruence, the reducibility and root-multiplicity facts,
and the elementary prime-cover obstruction all survive independent
derivation.  Their mathematical status remains `proof sketch`, not
`machine-checked`.

The theorem-applicability audit is `literature-checked`: the inspected
results average all roots or all degree-one ideals under quantifiers that do
not contain the BBP-selected root with its synchronized complementary
phases.  The independent finite replay is only an `experiment`.

The first missing implication is therefore exactly the one claimed as
missing by the primary artifact: there is no estimate for the full weighted
28-coordinate sum, and hence no forcing discrepancy, state target hitting,
or canonical V1 result.  V1 remains a `conjecture`.  This missing theorem is
not a fatal gap in the report because the report does not claim it.

## 1. Independent derivation of the 28 poles

Write

\[
 D_A=8k+1,\quad D_B=8k+5,\quad D_C=4k+3,\quad D_D=2k+1.
\]

Cross-multiplication, performed independently over the integer polynomial
ring, gives

\[
 \sum_{s\in\{A,B,C,D\}}c_s\prod_{t\ne s}D_t
 =240k^2+302k+94
 =2(120k^2+151k+47),
\]

for \((c_A,c_B,c_C,c_D)=(8,-2,-1,-1)\).  Therefore

\[
 2a(k)=\frac8{8k+1}-\frac2{8k+5}
       -\frac1{4k+3}-\frac1{2k+1}.
\]

Putting \(k=7n+j\), multiplying by
\(5^{n+1}16^{7-j}\), and summing over \(1\le j\le7\) produces exactly 28
indexed terms and exactly \(2b_n\).  No numerical interpolation is used in
this derivation.

The undoubled identity is

\[
 a(k)=\frac4{8k+1}-\frac1{8k+5}
      -\frac1{2(4k+3)}-\frac1{2(2k+1)}.
\]

The final two denominators are even, so their separate inverses modulo a
power of two do not exist.  The primary report's phrase “last-slot terms”
should be read as “last two partial-fraction terms”; this is a wording issue,
not a mathematical gap.

## 2. Why reduction modulo \(2M_n\) is exact

Let \(M=M_n\), \(N=2M\), and \(x=[b_n]_M\).  Since every denominator in
\(b_n\) is odd, \(b_n\) is two-integral.  Thus

\[
 b_n-x=M u\qquad(u\text{ two-integral}),
\]

and consequently

\[
 2b_n-2x=N u.
\]

Because \(0\le2x<N\), this proves the canonical-residue identity

\[
                   [2b_n]_N=2[b_n]_M.                 \tag{IA1}
\]

For a pole \(L=L_{n,j,s}\), put

\[
 q=5^{n+1}C_{j,s},\qquad
 \rho\equiv qL^{-1}\pmod N,\qquad
 h=\frac{L\rho-q}{N}.
\]

Every \(L\) is odd, so this definition is legal even when \(q<0\).  Direct
division gives

\[
 \frac\rho N=\frac hL+\frac q{LN}.                    \tag{IA2}
\]

Summing (IA2) over the 28 poles uses
\(\sum q/L=2b_n\) and yields

\[
 \sum\frac\rho N=\sum\frac hL+\frac{b_n}{M}.
\]

The fractional part of the left side is
\([2b_n]_N/N\), which equals \([b_n]_M/M=\Gamma_n\) by (IA1).  Hence the
primary report's formula

\[
 \Gamma_n=\left\{\sum_{j,s}\frac{h_{n,j,s}}{L_{n,j,s}}
                         +\frac{b_n}{M_n}\right\}
\]

is an exact identity.  The independent checker verifies it also at \(n=0\),
which the primary checker did not scan.

## 3. Distinguished root and polynomial

Modulo a prime pole \(p=L(n)=\alpha n+\beta\), away from 2 and 5,
\(N=2^{27(n+1)+1}\) gives

\[
 h\equiv-qN^{-1}
   \equiv-\frac C2\left(5\,2^{-27}\right)^{n+1}\pmod p. \tag{IA3}
\]

With \(B=5\,2^{-27}\) and \(r=B^n\), Fermat's theorem gives

\[
 r^\alpha=B^{\alpha n}=B^{p-\beta}
          \equiv B^{1-\beta}\pmod p.                 \tag{IA4}
\]

Thus (IA3) is a fixed nonzero multiple of the selected root (IA4).  Clearing
the denominator in (IA4) gives the primitive integer polynomial

\[
 F_{\alpha,\beta}(Y)
 =5^{\beta-1}Y^\alpha-2^{27(\beta-1)}.
\]

All \(\alpha\) are even and all \(\beta\) are odd, so the displayed
difference-of-squares factorization in the primary report is exact for all
28 forms.  For a primitive linear form, a root exists and the cyclic group
\(\mathbb F_p^*\) gives exactly

\[
 \gcd(\alpha,p-1)=\gcd(\alpha,\beta-1)
\]

roots.  Across the 24 primitive forms this ranges from 2 to 56.  Therefore
the exponential formula always selects one member of a non-singleton root
fibre; an all-root average cannot isolate it without an additional theorem.

One harmless precision point concerns the ideal-language sentence.  It is
read in the appropriate localized order and away from the finitely many
leading-coefficient, conductor, and discriminant primes.  Also, the
irreducible factor of the reducible natural polynomial that contains the
selected residue may vary with \(p\).  Either qualification only makes the
selection problem stricter and does not affect the no-go conclusion.

## 4. Reducibility and prime-cover obstruction

For a linear form \(\alpha n+\beta\), the exact fixed divisor is
\(\gcd(\alpha,\beta)\).  Independent enumeration gives precisely

\[
 A_6=56n+49,\quad B_2=56n+21,\quad
 C_1=28n+7,\quad D_3=14n+7,
\]

all with fixed divisor seven.  They are composite for every \(n\ge1\).
The other 24 forms are primitive.  For these, the three displayed witnesses

\[
 n\equiv0\pmod3:\ D_1=14n+3,\qquad
 n\equiv1\pmod3:\ B_1=56n+13,\qquad
 n\equiv2\pmod3:\ D_2=14n+5
\]

are divisible by three and exceed three at every applicable positive depth.
So at every \(n\ge1\), four fixed forms plus at least one distinct primitive
form are composite.  The all-28 and all-24 simultaneous-primality shortcuts
are refuted, while Dirichlet's theorem applies only one primitive form at a
time.  It supplies no simultaneous prime-tuple result.

## 5. Independent primary-source check

The four downloadable sources were fetched again from their primary
locations on 2026-08-13 UTC.  Their SHA-256 values exactly match the pins in
the primary report:

| source | independently checked quantifier | SHA-256 |
|---|---|---|
| Chunlin Wang, [arXiv:2108.05496](https://arxiv.org/pdf/2108.05496), Theorems 1.1--1.3 and 3.8 | The correspondence uses all roots/all degree-one ideals; Theorem 1.2 orders all degree-one ideals by norm. Theorem 3.8 requires cumulative root/ideal mass \(>cx\). Prime norms have only \(O(x/\log x)\) such mass for a fixed field, and the paper explicitly separates prime ideals as another question. | `78565fd47fda2ec5060fe67b0bdf75ff552ecd891cdc2c5851f1d1d7124dbd26` |
| Sa'ar Zehavi, [arXiv:2003.13100](https://arxiv.org/pdf/2003.13100), Theorems 1.1--1.2 | Hooley's theorem is stated for the concatenation of every root at every integer modulus. The joint theorem uses the full Cartesian root product at one common integer modulus. The paper gives an explicit failure of prime-modulus joint equidistribution for \(f=g=x^2+1\). | `82d654c51f7997269d013db30f3fcb03e40ef4c50083e790255cbdd9c11f0e18` |
| Hieu T. Ngo, [arXiv:2107.13301](https://arxiv.org/pdf/2107.13301), introduction and Theorem 1.1 | The quadratic harmonic \(\rho_h(n)\) is explicitly the sum over every root modulo \(n\). The DFI and Tóth estimates are stated for the associated all-root Weyl form. | `113f94cae375573f9ff9fe427e378ea01975befb42805ee54dcf79377108bc99` |
| Timothy Foo, [Acta Arithmetica 144 (2010)](https://doi.org/10.4064/aa144-1-1), main theorem | Conditional on Bouniakowsky, the union of all normalized roots over prime moduli is dense. It is neither an unconditional discrepancy theorem nor a selected-root theorem. | `72a3829132d72ee414dd3ed740eba390c36db4764f5023dc1d7bb58691edb831` |

The official Hooley and Duke--Friedlander--Iwaniec publication records were
also checked.  Their older complete scans were not newly available from
those pages; the exact relevant quantifiers were independently confirmed in
the pinned Zehavi and Ngo papers.  This matches the primary report's explicit
disclosure and does not create an invented source pin.

The applicability verdict is therefore correct:

- Hooley and Wang average all roots or all degree-one ideals over integer
  moduli, not the BBP-selected root on an affine prime subsequence.
- DFI, Tóth, and Ngo concern irreducible quadratics and all their roots; the
  natural BBP polynomial is reducible of degree 14, 28, or 56.
- Wang and Zehavi's joint results use all Cartesian root tuples at the same
  modulus, whereas the BBP terms have 28 different linear moduli and one
  selected coordinate in each fibre.
- Foo is conditional, proves only density of the union of all prime roots,
  and supplies no correlated weight estimate.

Finally, the primary report's complementary-weight counterexample is exact:
if \(z_n\) is one unit phase, the unit weight \(\overline{z_n}\) makes every
weighted term equal to one.  It does not claim that the actual BBP complement
has this form; it correctly shows that an unweighted marginal theorem alone
cannot handle an arbitrary synchronized complement.

## 6. Independent checker

The checker
[bbp_dyadic_distinguished_root_20260813_independent_check.py](bbp_dyadic_distinguished_root_20260813_independent_check.py),
SHA-256
`fdd1fec1266f6e471ec2f56123ffd1ac8e57fe3baaee94a245d981df0d2294d3`,
uses only the Python standard library and imports no branch checker.  It
cross-multiplies the rational function in the integer polynomial ring,
checks the exact residue lift through depth 120 including \(n=0\), enumerates
72 complete prime root fibres, and independently scans all primitive forms
through depth 3000.

Run from the repository root:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_dyadic_distinguished_root_20260813_independent_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_dyadic_distinguished_root_20260813_independent_check.py
```

Retained result:

```text
status: PASS_INDEPENDENT_NO_FATAL_GAP_NO_DISTRIBUTION_BRIDGE
bounded_replay_label: experiment
algebraic_claim_label: proof sketch
literature_audit_label: literature-checked
exact_depth_range_including_zero: [0, 120]
partial_fraction_checks: 847
exact_doubled_residue_checks: 121
exact_phase_reconstruction_checks: 121
exact_lift_checks: 3388
prime_root_checks_in_exact_scan: 934
enumerated_root_set_checks: 72
factorization_checks: 28
pole_form_count: 28
permanently_composite_forms: [A6, B2, C1, D3]
prime_capable_form_count: 24
minimum_root_multiplicity: 2
maximum_root_multiplicity: 56
prime_instances: 16130
asserts_selected_root_equidistribution: false
asserts_gamma_discrepancy: false
asserts_state_target_hitting: false
asserts_v1: false
```

The independent result supports the primary artifact's deliberately limited
endpoint: exact structural information and a `literature-checked`
applicability no-go, but no proof of decimal block occurrence in pi.
