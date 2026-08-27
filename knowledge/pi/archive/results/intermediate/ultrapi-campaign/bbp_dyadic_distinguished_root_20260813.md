# BBP dyadic forcing: 28 linear poles and distinguished roots

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The target is Marcel's local, human-authored question and has no external
source URL; none is invented here.

Frozen branch inputs:

- [bbp_dyadic_diagonal_functional_recurrence_20260813.md](bbp_dyadic_diagonal_functional_recurrence_20260813.md),
  SHA-256
  `8768abbdd38d21721955f76a0c1ba90054ed9177a95b9b393aa393fc0d7466ba`;
- [bbp_dyadic_diagonal_functional_recurrence_20260813_check.py](bbp_dyadic_diagonal_functional_recurrence_20260813_check.py),
  SHA-256
  `c7d04bb733cf50b08ed46dddf52bb98bbe726c0897f74c93f00533313a67f651`.

## Outcome and claim boundary

The 28-pole idea yields a complete exact algebraic reduction, with status
`proof sketch`, and two sharp no-go findings.

1. Doubling the forcing before reducing it gives an exact sum of 28 phases
   with odd linear denominators.  This avoids an invalid termwise division
   by two modulo the original dyadic modulus.
2. If one of those linear denominators is prime, its selected rational-base
   residue is indeed a distinguished root of a fixed polynomial congruence.
3. The root relation is never simultaneously available for all 28 terms:
   four linear forms are always composite, and the other 24 have a local
   obstruction modulo three.
4. Hooley, Duke--Friedlander--Iwaniec, Wang, and the inspected joint-root
   results average **all** roots over **all** moduli or all prime moduli.
   They do not estimate the one root selected by the exponential formula.
   Wang's ideal theorem likewise averages all degree-one ideals, not the
   selected degree-one prime ideal.
5. Even an unweighted discrepancy theorem for one selected root cannot
   survive an arbitrary complementary phase: the complementary unit weight
   can cancel that phase identically.  The actual BBP complement is not
   arbitrary, but none of the inspected theorems controls its correlation.

Consequently no discrepancy estimate for the full forcing
\(\Gamma_n\), no target-hitting statement for \(X_n\), and no canonical V1
implication is obtained.  V1 remains a `conjecture`.  The source audit is
`literature-checked`; bounded calculations are `experiment`.  Nothing here
is `machine-checked`, a `candidate resolution`, or a `verified resolution`.

## 1. Normalized question and ambiguous quantifiers

Canonical V1 asks whether every finite decimal word, with leading zeroes
allowed, occurs contiguously in the decimal expansion of pi.  The empty word
is vacuous.  This branch asks only whether a particular dyadic coordinate can
be shown to hit prescribed intervals.

The frozen recurrence is

\[
 X_{n+1}=\{10X_n+\Gamma_n\}.                         \tag{DR1}
\]

There are two distinct possible distribution targets:

\[
 \sum_{n<N}e(q\Gamma_n)=o(N)                         \tag{DR2}
\]

would make the forcing equidistributed, while

\[
 \sum_{n<N}e(qX_n)=o(N)                              \tag{DR3}
\]

would make the state equidistributed.  Here \(q\ne0\) is fixed and
\(e(t)=\exp(2\pi it)\).  Either is stronger than mere target hitting, and
neither is established.

The quantifiers that must not be conflated are:

- all roots of a congruence versus one distinguished root;
- all integer moduli versus prime moduli versus primes in one progression;
- one root coordinate versus the joint 28-coordinate vector;
- a fixed test phase versus an arbitrary or correlated complementary phase;
- discrepancy of \(\Gamma_n\) versus discrepancy or hitting by \(X_n\).

## 2. Exact 28-linear-denominator formula

Retain the frozen coefficient

\[
 a(k)=\frac{120k^2+151k+47}
 {(2k+1)(4k+3)(8k+1)(8k+5)}.                        \tag{DR4}
\]

Direct cross multiplication gives

\[
 2a(k)=\frac8{8k+1}-\frac2{8k+5}
       -\frac1{4k+3}-\frac1{2k+1}.                  \tag{DR5}
\]

For \(s\in\{A,B,C,D\}\), define

\[
\begin{array}{c|c|c|c}
s&\lambda_s&\mu_s&c_s\\ \hline
A&8&1&8\\
B&8&5&-2\\
C&4&3&-1\\
D&2&1&-1
\end{array}                                         \tag{DR6}
\]

and, for \(1\le j\le7\), put

\[
 L_{n,j,s}=\lambda_s(7n+j)+\mu_s
            =\alpha_sn+\beta_{j,s},\qquad
 C_{j,s}=c_s16^{7-j},                               \tag{DR7}
\]

where \(\alpha_s=7\lambda_s\) and
\(\beta_{j,s}=\lambda_sj+\mu_s\).  Every
\(L_{n,j,s}\) is odd.  If

\[
 b_n=5^{n+1}\sum_{j=1}^716^{7-j}a(7n+j),\qquad
 M_n=2^{27(n+1)},                                   \tag{DR8}
\]

then (DR5) gives the exact 28-pole identity

\[
 \boxed{
 2b_n=5^{n+1}\sum_{j=1}^7\sum_s
                  \frac{C_{j,s}}{L_{n,j,s}}.}       \tag{DR9}
\]

The doubling is essential.  The last-slot terms in the undoubled partial
fractions have coefficient \(-1/2\), so their denominators are not units
modulo \(M_n\).  They cannot be reduced separately modulo \(M_n\).

Instead set \(N_n=2M_n\) and, for every pair \((j,s)\), define

\[
\begin{aligned}
 q_{n,j,s}&=5^{n+1}C_{j,s},\\
 \rho_{n,j,s}&\equiv q_{n,j,s}L_{n,j,s}^{-1}\pmod {N_n},
       \quad0\le\rho_{n,j,s}<N_n,\\
 h_{n,j,s}&=\frac{L_{n,j,s}\rho_{n,j,s}-q_{n,j,s}}{N_n}.
\end{aligned}                                       \tag{DR10}
\]

All inverses in (DR10) exist.  Since \(b_n\) is two-integral,

\[
 [2b_n]_{N_n}=2[b_n]_{M_n}.                          \tag{DR11}
\]

Also

\[
 \frac{\rho_{n,j,s}}{N_n}
 =\frac{h_{n,j,s}}{L_{n,j,s}}
  +\frac{q_{n,j,s}}{L_{n,j,s}N_n}.                  \tag{DR12}
\]

Summing (DR12), using (DR9), and reducing modulo one proves

\[
 \boxed{
 \Gamma_n=\left\{
   \sum_{j=1}^7\sum_s\frac{h_{n,j,s}}{L_{n,j,s}}
   +\varepsilon_n\right\},
 \qquad \varepsilon_n=\frac{b_n}{M_n}.}             \tag{DR13}
\]

Thus (DR13) is the safe 28-linear-denominator refinement of the frozen
seven-product formula.  It is an identity of the complete forcing, not an
approximation; only \(\varepsilon_n\) is archimedean-small.

## 3. The distinguished-root congruence

Fix a pair \((j,s)\), abbreviate

\[
 L(n)=\alpha n+\beta,qquad C=C_{j,s},qquad
 B=5\,2^{-27}.                                      \tag{DR14}
\]

Let \(p=L(n)\) be prime, excluding the finite primes dividing \(10C\).
Equation (DR10) gives

\[
 h_{n,j,s}\equiv-\frac C2 B^{n+1}pmod p.           \tag{DR15}
\]

Put \(r_{n,p}=B^n\pmod p\).  Since
\(p=\alpha n+\beta\), Fermat's theorem gives

\[
 \boxed{
 r_{n,p}^{\alpha}=B^{\alpha n}
 =B^{p-\beta}\equiv B^{1-\beta}\pmod p.}           \tag{DR16}
\]

Thus \(r_{n,p}\) is a distinguished root of the fixed rational polynomial

\[
 R_{\alpha,\beta}(Y)=Y^\alpha-B^{1-\beta},          \tag{DR17}
\]

and \(h_{n,j,s}\bmod p\) is its fixed nonzero rational multiple
\(-(C/2)B\).  Equivalently it is a root of another fixed scaled polynomial.

Clearing denominators in (DR17) gives the primitive integer polynomial

\[
 F_{\alpha,\beta}(Y)
 =5^{\beta-1}Y^\alpha-2^{27(\beta-1)}.              \tag{DR18}
\]

This natural polynomial does **not** meet Hooley's irreducibility premise.
Every \(\alpha\) is even and every \(\beta\) is odd, so

\[
 F_{\alpha,\beta}(Y)
 =\left(5^{(\beta-1)/2}Y^{\alpha/2}
        -2^{27(\beta-1)/2}\right)
  \left(5^{(\beta-1)/2}Y^{\alpha/2}
        +2^{27(\beta-1)/2}\right).                 \tag{DR19}
\]

For a prime-capable form, \((\alpha,\beta)=1\).  Because a root exists,
cyclicity of \(\mathbb F_p^*\) shows that (DR16) has exactly

\[
 \gcd(\alpha,p-1)=\gcd(\alpha,\beta-1)              \tag{DR20}
\]

roots.  This number ranges from 2 to 56 across the 24 forms and is never
one.  Formula (DR16) selects one of those roots; an all-root exponential
sum does not isolate it.

The ideal interpretation is exact but does not remove this selection.  If
\(\vartheta\) is an algebraic root of an irreducible factor containing the
selected residue, then \((p,\vartheta-r_{n,p})\) is the corresponding
degree-one prime ideal.  The exponential formula selects this ideal from
the ideals above \(p\); it does not average over all of them.

## 4. Exact prime-selection obstructions

The four families are

\[
\begin{array}{c|c|c}
s&L_{n,j,s}&C_{j,s}\\ \hline
A&56n+8j+1&8\,16^{7-j}\\
B&56n+8j+5&-2\,16^{7-j}\\
C&28n+4j+3&-16^{7-j}\\
D&14n+2j+1&-16^{7-j}.
\end{array}                                         \tag{DR21}
\]

Four forms have a fixed divisor seven:

\[
 A_6=56n+49,quad B_2=56n+21,quad
 C_1=28n+7,quad D_3=14n+7.                         \tag{DR22}
\]

They are composite for every \(n\ge1\).  Even after deleting them, the
remaining 24 forms cannot be prime simultaneously.  A three-line covering
argument is enough:

\[
\begin{array}{c|c}
n\pmod3&\text{a remaining form divisible by }3\\ \hline
0&D_1=14n+3\\
1&B_1=56n+13\\
2&D_2=14n+5.
\end{array}                                         \tag{DR23}
\]

For \(n\ge1\), the displayed divisible value is larger than three whenever
its row applies.  Hence at least five of the 28 denominators are composite
at every positive depth.  There is no subsequence on which all 28 uses of
Fermat's theorem in (DR16) are simultaneously legitimate.

For each one of the 24 primitive linear forms, Dirichlet's theorem does give
infinitely many prime values.  That only exposes one root coordinate and
leaves 27 correlated phases.  Simultaneous primality of a chosen admissible
set of two or more distinct forms is a prime-tuple problem and is not
supplied by Dirichlet's theorem.  The all-28 and all-24 versions are stronger
than unproved: (DR22)--(DR23) refute them outright.

## 5. Theorem-by-theorem applicability audit

Status: bounded `literature-checked` search and direct inspection on
**2026-08-13 UTC**.

| result | what the theorem actually averages | applicability here |
|---|---|---|
| Hooley, Theorem 2 (1964) | For one fixed primitive irreducible polynomial of degree greater than one, concatenate **all roots modulo every positive integer modulus**; the normalized roots are uniformly distributed. | (DR18) is reducible. More decisively, the BBP formula chooses one root only on sparse prime values of \(L(n)\). Neither root selection nor prime sparsity is covered. |
| Duke--Friedlander--Iwaniec (1995) | For an irreducible quadratic of negative discriminant, the roots over prime moduli are equidistributed. Their Weyl harmonic sums over **all roots**; Ngo records the DFI Proposition 1 bound explicitly. | The natural polynomial has degree 14, 28, or 56 and is reducible. Even if an irreducible quadratic factor is isolated on a subsequence, DFI averages both roots and does not estimate the exponential rule selecting one of them. |
| Tóth/Ngo quadratic extension | Treats irreducible quadratics of positive discriminant, again through a harmonic summing every root. | Same all-roots/selected-root failure; no 28-coordinate or complementary-weight estimate. |
| Wang, Theorem 1.1 | Roots of a fixed minimal polynomial modulo \(m\) correspond to **all** degree-one ideals of norm \(m\), away from finitely many primes. | It validates the ideal dictionary, but the BBP exponent chooses one ideal above each eligible prime. |
| Wang, Theorem 1.2 | Residues of an irrational algebraic number over **all degree-one ideals**, ordered by norm, are uniformly distributed. | It cannot be restricted to the selected degree-one prime ideal. Wang explicitly lists prime ideals as a separate question. |
| Wang, Theorem 3.8 | Restricts norms to a set \(A\) only when the cumulative number of degree-one ideals over \(m\in A\), \(m\le x\), is bounded below by \(cx\). | Prime norms have only \(O(x/\log x)\) members, so the hypothesis fails before root selection is considered. |
| Wang, Theorem 1.3; Zehavi, Theorem 1.2 | Joint distribution of the full Cartesian product of roots of fixed polynomials at the **same integer modulus**, over all integer moduli. | The 28 moduli in (DR21) differ, and the formula takes one selected coordinate rather than every Cartesian tuple. Zehavi explicitly shows that prime-modulus joint distribution can fail even for a pair. |
| Foo (2010) | Conditional on Bouniakowsky, the union of **all** normalized roots of a fixed irreducible polynomial over prime moduli is dense. | It is conditional, gives density rather than the required weighted discrepancy, and still does not select the BBP root. |

The official Hooley and DFI publication pages were inspected directly.  The
closed older scans were not assigned invented PDF hashes.  Their exact
quantifier scopes were cross-checked in the directly inspected Wang, Zehavi,
Ngo, and Foo PDFs listed in section 8.

The key distinction can already be seen for a quadratic with roots
\(\{u,-u\}\).  Equidistribution of the multiset containing both roots does
not imply equidistribution of a rule choosing one: choosing the least of the
two representatives would confine the result to \([0,1/2]\).  The BBP
choice is different, but an all-root theorem needs an additional selection
argument before it says anything about that choice.

Chebotarev-type information about the power-residue symbol is also not the
missing statement.  It can distribute finitely many Frobenius or symbol
classes.  It does not locate the least representative of the selected root
at archimedean scale \(p\), which is the content of \(r_{n,p}/p\).

## 6. Why an arbitrary complementary phase is fatal

Equation (DR13) gives, for every fixed nonzero integer \(q\),

\[
 e(q\Gamma_n)=e(q\varepsilon_n)
 \prod_{j=1}^7\prod_s
 e\!\left(q\frac{h_{n,j,s}}{L_{n,j,s}}\right).       \tag{DR24}
\]

Suppose one factor is denoted \(z_n\) and the product of the other factors
is denoted \(W_n\), with \(|W_n|=1\).  An unweighted root theorem could at
best control \(\sum z_n\).  It gives no estimate for
\(\sum W_nz_n\) with arbitrary weights: choosing

\[
                         W_n=\overline{z_n}           \tag{DR25}
\]

makes every summand equal to one.  This is an exact counterexample to any
inference that one locally equidistributed root remains cancelling against
an arbitrary complementary phase.

The BBP complement in (DR24) is fixed rather than arbitrary, so (DR25) is
an applicability no-go, not a theorem that the actual sum is large.  To
prove (DR2), one needs cancellation for the actual full synchronized
product.

The state requires one more correlated factor.  From (DR1) and (DR24),

\[
 e(qX_{n+1})=e(10qX_n)e(q\varepsilon_n)
 \prod_{j=1}^7\prod_s
 e\!\left(q\frac{h_{n,j,s}}{L_{n,j,s}}\right).       \tag{DR26}
\]

Thus even discrepancy of \(\Gamma_n\) as a marginal would not by itself
prove (DR3).  The needed estimate is weighted by the state
\(e(10qX_n)\), which is generated from the same preceding forcing and is
not independent.

Full joint equidistribution of the 28 selected coordinates would push
forward to equidistribution of their sum and would address (DR24), but none
of the inspected theorems supplies that vector.  Equations (DR22)--(DR23)
also prevent obtaining all 28 coordinates by simply restricting to depths
where all denominators are prime.

## 7. Exact remaining estimates

The clean forcing target is the `conjecture`

\[
 \forall q\in\mathbb Z\setminus\{0\}:\quad
 \sum_{n<N}e(q\varepsilon_n)
 \prod_{j=1}^7\prod_s
 e\!\left(q\frac{h_{n,j,s}}{L_{n,j,s}}\right)=o(N). \tag{DR27}
\]

The corresponding state target is the strictly more coupled `conjecture`

\[
 \forall q\in\mathbb Z\setminus\{0\}:\quad
 \sum_{n<N}e(10qX_n)e(q\varepsilon_n)
 \prod_{j=1}^7\prod_s
 e\!\left(q\frac{h_{n,j,s}}{L_{n,j,s}}\right)=o(N). \tag{DR28}
\]

The distinguished-root identity (DR16) controls only one factor on a sparse
prime subsequence.  It does not imply either conjecture.  A useful future
theorem would have to handle the selected root, composite complementary
moduli, different linear forms at the same depth, and the actual correlated
weight in (DR27) or (DR28).

## 8. Sources inspected

| source | directly checked content | source pin |
|---|---|---|
| C. Hooley, [*On the distribution of the roots of polynomial congruences*](https://doi.org/10.1112/S0025579300003466), Mathematika 11 (1964), 39--49 | Official Cambridge extract states primitive irreducible degree \(>1\), all roots, and variable integer modulus. Theorem 2 scope is reproduced in Zehavi Theorem 1.1. | Official publication page; older full scan is access-controlled, so no PDF hash is claimed. |
| W. Duke, J. Friedlander, H. Iwaniec, [*Equidistribution of roots of a quadratic congruence to prime moduli*](https://annals.math.princeton.edu/1995/141-2/p08), Annals of Mathematics 141 (1995), 423--441 | Official Annals record checked. The exact all-root Weyl harmonic and DFI Proposition 1 scope were cross-checked in Ngo, pp. 1--2. | Official publication page; older full scan is closed, so no PDF hash is claimed. |
| Chunlin Wang, [*Distribution of residues of an algebraic number modulo ideals of degree one*](https://arxiv.org/pdf/2108.05496), Theorems 1.1--1.3 and 3.8 | All degree-one ideals; positive-linear-density norm subsets; explicitly separates the prime-ideal question. | SHA-256 `78565fd47fda2ec5060fe67b0bdf75ff552ecd891cdc2c5851f1d1d7124dbd26` |
| Sa'ar Zehavi, [*On the Joint Distribution of the Roots of Pairs of Polynomial Congruences*](https://arxiv.org/pdf/2003.13100), Theorems 1.1--1.2 | Full Cartesian root pairs, same modulus, all integer moduli; explicit prime-joint counterexample. | SHA-256 `82d654c51f7997269d013db30f3fcb03e40ef4c50083e790255cbdd9c11f0e18` |
| Hieu T. Ngo, [*On Roots of Quadratic Congruences*](https://arxiv.org/pdf/2107.13301), introduction and Theorem 1.1 | Defines the all-root harmonic, records the DFI negative-discriminant bound, and treats positive-discriminant quadratics. | SHA-256 `113f94cae375573f9ff9fe427e378ea01975befb42805ee54dcf79377108bc99` |
| Timothy Foo, [*The Bouniakowsky conjecture and the density of polynomial roots to prime moduli*](https://doi.org/10.4064/aa144-1-1), main theorem | General irreducible-polynomial prime-root density is conditional and concerns the union of all roots. | SHA-256 `72a3829132d72ee414dd3ed740eba390c36db4764f5023dc1d7bb58691edb831` |

The repository and mathlib search found elementary polynomial-root,
Dirichlet-primes-in-progressions, and already formalized Weyl-to-decimal
interfaces, but no formal Hooley, DFI, Wang, selected-root, or weighted
28-coordinate theorem.  No verified-track declaration is added.

## 9. Independent checker

The companion
[bbp_dyadic_distinguished_root_20260813_check.py](bbp_dyadic_distinguished_root_20260813_check.py),
SHA-256
`e7103ffab23b88fb5bdf83fab73bcc1979f2ce3075dce2740d074d65f3b2b304`,
imports no branch checker.  It symbolically verifies (DR5), reconstructs
(DR9)--(DR13) exactly, checks the root and scaled-lift congruences, verifies
the fixed-divisor and modulo-three obstructions, and scans the selected
roots only as `experiment`.

Run from the repository root:

```bash
.venv/bin/python \
  work/ultrapi-resume/bbp_dyadic_distinguished_root_20260813_check.py \
  --exact-max-depth 80 --prime-scan-max-depth 5000
```

Retained output:

```text
status: PASS_NO_APPLICABLE_ROOT_EQUIDISTRIBUTION_BRIDGE
bounded_replay_label: experiment
analytic_claim_label: proof sketch
exact_depth_range: [1, 80]
prime_scan_depth_range: [1, 5000]
symbolic_partial_fraction_checks: 1
pole_form_count: 28
exact_partial_fraction_checks: 560
exact_gamma_checks: 80
exact_lift_checks: 2240
exact_prime_root_checks: 645
reducible_natural_root_polynomials: 28
permanently_composite_forms: [A6, B2, C1, D3]
prime_capable_form_count: 24
prime_instances: 25636
root_identity_checks: 25636
root_multiplicity_checks: 25636
adversarial_complement_checks: 25636
minimum_roots_of_natural_congruence: 2
maximum_roots_of_natural_congruence: 56
minimum_family_prime_count: 1002
maximum_family_prime_count: 1165
minimum_observed_family_star_discrepancy: 0.012353889293713421
maximum_observed_family_star_discrepancy: 0.04429888292369905
asserts_distinguished_root_equidistribution: false
asserts_gamma_discrepancy: false
asserts_x_target_hitting: false
asserts_v1: false
```

The finite discrepancies are compatible with eventual equidistribution,
nonuniformity, or slow convergence.  They carry no proof leverage.

## 10. Coordination record

This branch registered descendant-area watch
`watch:local:pi-digits:distinguished-root-partial-fraction-20260813` on
`local:pi-digits` for agent
`codex-distinguished-root-partial-fraction`.  Its initial poll was empty at
cursor and delivered sequence 57,251; no observation event was used as
evidence and none was acknowledged.

The exact 28-pole formula and distinguished-root congruence are useful
structural information.  The theorem audit and the prime-cover obstruction
show precisely why they do not yet become a discrepancy theorem.  No V1
claim is made.
