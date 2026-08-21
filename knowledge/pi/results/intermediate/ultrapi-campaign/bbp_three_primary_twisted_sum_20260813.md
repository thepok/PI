# BBP three-primary complete grid: exact Fourier reduction and the twisted-complement barrier

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable target is Marcel's local question and has no external source URL;
none is invented here.

Frozen inputs:

- [bbp_three_primary_epoch_20260813.md](bbp_three_primary_epoch_20260813.md),
  SHA-256
  `5b34ceb3aa2857b9227cce5ac7ae84cafbbac47d2c12adf889c37f11280d6fd7`;
- [bbp_large_sieve_short_orbit_20260813.md](bbp_large_sieve_short_orbit_20260813.md),
  SHA-256
  `23b3cba4c2b7c5846b4b18748994db8c9e897725612eaf80d08b32b3a97b781d`;
- [T73T73ThreePrimaryOrbit.lean](../../TheoryLib/PiQuantitativeBlockHitting/T73T73ThreePrimaryOrbit.lean),
  SHA-256
  `1499b29893a05fe91d64ee468ff320f0f59c23eb07f13220dab64b9fbfe23009`.

All three inputs remained byte-for-byte unchanged in this branch.

## Outcome and claim boundary

Canonical V1 remains a `conjecture`.  This report does not prove a complete
BBP return, density of the decimal orbit, normality of pi, or occurrence of
every finite decimal word.

The branch has three exact conclusions, each with label `proof sketch`.

1. On one complete three-primary period, the **entire** BBP phase is exactly
   one selected Fourier coefficient of the complementary CRT phase after a
   nonlinear three-adic logarithm permutation.  This is an identity, not an
   approximation.
2. In the original exponent coordinate, the isolated three-primary phase has
   an exact sparse Fourier transform.  For \(E\ge4\) and
   \(T=3^{E-2}\), its transform is supported on one residue class modulo 9;
   every nonzero coefficient has magnitude \(3\sqrt T\).
3. Consequently, any complementary weight with bounded Fourier-algebra norm
   receives square-root cancellation.  The actual BBP complement is not
   known to have that bound.  Its modulus, period, factor count, and dyadic
   nonunit part all grow with the row.

The exact reduction also supplies a sharp no-go.  Character orthogonality
controls the average over all artificial Fourier frequencies, but the BBP
phase selects one frequency correlated with the same numerator and
denominator.  Orthogonality alone gives no bound at that selected frequency;
a unit-modulus complementary weight can saturate it term by term.

The companion bounded replay has label `experiment`.  The source
applicability audit in Section 7 has label `literature-checked`.  This branch
adds no formal declaration and makes no new `machine-checked`,
`candidate resolution`, or `verified resolution` claim.

## 1. Normalized target and quantifiers

Canonical V1 means:

> For every integer \(P\ge1\) and every \(k\) with
> \(0\le k<10^P\), there is an integer \(n\ge0\) such that the block of
> \(P\) decimal digits of pi beginning at position \(n+1\), with leading
> zeros retained, is the base-ten word represented by \(k\).

Equivalently,

\[
 \left\lfloor 10^P\{10^n\pi\}\right\rfloor=k.       \tag{TS1}
\]

The quantifier is over finite words and asks for at least one occurrence; it
does not quantify over infinite digit strings and does not itself assert
infinitely many occurrences.  The present branch concerns only a proposed
BBP route to (TS1).  A complete grid in one CRT coordinate is not a complete
grid for the sum of all coordinates.

## 2. Exact CRT factorization of one complete three-primary row

Write the reduced BBP partial sum as

\[
 B_M={P_M\over 3^{E_M}C_M},\qquad
 (P_M,3C_M)=1,\qquad(3,C_M)=1.                     \tag{TS2}
\]

Fix a row with \(E=E_M\ge4\), put

\[
 q_3=3^E,\qquad T=3^{E-2},\qquad C=C_M,            \tag{TS3}
\]

and use \(e_q(x)=\exp(2\pi i x/q)\).  Define the two primitive CRT
coefficients

\[
 \beta\equiv P_MC^{-1}\pmod {q_3},\qquad
 \kappa\equiv P_Mq_3^{-1}\pmod C.                 \tag{TS4}
\]

For every integer \(N\), the Chinese remainder theorem gives

\[
 e_{q_3C}(P_MN)=e_{q_3}(\beta N)e_C(\kappa N).     \tag{TS5}
\]

Indeed, the numerator on the right over the common denominator is
\(\beta NC+\kappa Nq_3\), which is congruent to \(P_MN\) modulo both
coprime factors.  In particular, for any integer harmonic \(h\),

\[
 e\!\left(h(10^n-16)B_M\right)
 =e_{q_3}\!\left(h\beta(10^n-16)\right)
  e_C\!\left(h\kappa(10^n-16)\right).              \tag{TS6}
\]

For every integer \(n\ge0\), define

\[
 r_E(n)\equiv {10^n-1\over9}\pmod T.              \tag{TS7}
\]

The quotient is integral.  The exact order
\(\operatorname{ord}_{3^E}(10)=T\) shows that on any \(T\) consecutive
exponents \(r_E\) is a bijection onto \(\mathbb Z/T\mathbb Z\).  To see the
last step directly,

\[
 r_E(n)=r_E(m)\pmod T
 \iff 10^n=10^m\pmod {3^E}
 \iff n=m\pmod T.                                  \tag{TS8}
\]

Fix a starting exponent \(n_0\ge0\), and let
\(\nu_{E,n_0}(r)\in\{n_0,\ldots,n_0+T-1\}\) be the unique inverse in
(TS8).  Pull the complementary phase back to the additive grid by

\[
 W_{M,h,n_0}(r)=
 e_C\!\left(h\kappa
   (10^{\nu_{E,n_0}(r)}-16)\right).                \tag{TS9}
\]

Since \(10^n-16\equiv9r_E(n)-15\pmod {3^E}\), (TS6)--(TS9) yield the exact
identity

\[
 \boxed{
 \sum_{n=n_0}^{n_0+T-1}e\!\left(h(10^n-16)B_M\right)
 =e_{3^E}(-15h\beta)
  \sum_{r\bmod T}e_T(h\beta r)W_{M,h,n_0}(r).}     \tag{TS10}
\]

Normalize the additive Fourier transform by

\[
 \mathcal F_TW(k)={1\over T}
   \sum_{r\bmod T}W(r)e_T(-kr).                    \tag{TS11}
\]

Then (TS10) is simply

\[
 {1\over T}\sum_{n=n_0}^{n_0+T-1}
 e\!\left(h(10^n-16)B_M\right)
 =e_{3^E}(-15h\beta)
   \mathcal F_TW_{M,h,n_0}(-h\beta).               \tag{TS12}
\]

This is the requested exact orthogonality reduction.  For \(3\nmid h\),
the selected character \(r\mapsto e_T(h\beta r)\) is primitive because
\(\beta\) is a unit.  For general fixed \(h\ne0\), its conductor is
\(T/(T,h)\), which still tends to infinity when \(E\to\infty\).

## 3. Why ordinary orthogonality does not finish the row

Because \(|W(r)|=1\), Parseval applied to (TS11) says

\[
 \sum_{k\bmod T}|\mathcal F_TW(k)|^2=1.            \tag{TS13}
\]

Thus a frequency chosen independently and uniformly from all \(T\)
frequencies has mean squared coefficient \(1/T\).  The BBP row does not make
that independent choice.  It selects the single frequency
\(-h\beta_M\), while \(W_{M,h,n_0}\) is built from the same
\(P_M,C_M,h\), and exponent window.

This logical gap is sharp.  For any unit \(\beta\), the artificial
unit-modulus weight

\[
                         W(r)=e_T(-h\beta r)        \tag{TS14}
\]

makes the right side of (TS10) have magnitude exactly \(T\).  Equation
(TS14) is not asserted to be the BBP complement.  It proves that complete
grid coverage plus character orthogonality, with no structural information
about the complementary weight, cannot imply cancellation.

The inverse \(\nu_{E,n_0}\) also explains why the remaining coefficient is
not an ordinary Gauss sum.  The map \(n\mapsto r_E(n)\) obeys the formal-group
law

\[
 r_E(n+m)=r_E(n)+r_E(m)+9r_E(n)r_E(m)\pmod T,      \tag{TS15}
\]

not ordinary addition.  Multiplicative characters of the power orbit are
linear in \(n\), whereas (TS11) is Fourier analysis in the ordinary additive
coordinate \(r\).  The selected complement is therefore a three-adic
logarithm permutation followed by reduction of \(10^n\) modulo a changing
coprime modulus.  No polynomial, rational, or multiplicative-character form
for this pulled-back phase is established here.

## 4. Exact sparse Fourier transform in the exponent coordinate

There is nevertheless more cancellation structure than the grid statement
alone exposes.  Let \(a\) be prime to 3 and define, on
\(\mathbb Z/T\mathbb Z\),

\[
 f_{E,a}(j)=e_{3^E}(a10^j),\qquad
 \widehat f_{E,a}(\ell)=
   \sum_{j\bmod T}f_{E,a}(j)e_T(-\ell j).          \tag{TS16}
\]

### `proof sketch`

For every \(E\ge4\),

\[
 \boxed{
 |\widehat f_{E,a}(\ell)|^2=
 \begin{cases}
 9T,&\ell\equiv a\pmod9,\\
 0,&\ell\not\equiv a\pmod9.
 \end{cases}}                                      \tag{TS17}
\]

Thus exactly \(T/9\) Fourier coefficients survive and each has magnitude
\(3\sqrt T\).

Here is an elementary derivation.  The circular autocorrelation is

\[
 \begin{aligned}
 C_a(d)
 &=\sum_{j\bmod T}f_{E,a}(j+d)\overline{f_{E,a}(j)}\\
 &=\sum_{j\bmod T}
   e_{3^E}\!\left(a10^j(10^d-1)\right).            \tag{TS18}
 \end{aligned}
\]

As \(j\) runs modulo \(T\), write \(10^j=1+9r\); by (TS8), \(r\) runs
once modulo \(T\).  Additive-character orthogonality gives

\[
 C_a(d)=e_{3^E}\!\left(a(10^d-1)\right)
 \begin{cases}
 T,&T\mid10^d-1,\\
 0,&T\nmid10^d-1.
 \end{cases}                                      \tag{TS19}
\]

Put \(H=T/9=3^{E-4}\).  The order of 10 modulo \(T=3^{E-2}\) is \(H\), so
the nonzero cases are exactly \(d=mH\), \(0\le m<9\).  The binomial theorem
gives

\[
 10^H\equiv1+3^{E-2}\pmod {3^E},\qquad
 10^{mH}\equiv1+m3^{E-2}\pmod {3^E}.              \tag{TS20}
\]

For the first congruence, the linear term in
\((1+9)^H\) is \(9H=3^{E-2}\).  Every term of degree at least two is
divisible by \(3^E\): for \(H=3^r\) and \(2\le k\le H\),
\(v_3\binom{3^r}{k}\ge r-v_3(k)\), while
\(2k-v_3(k)\ge4\).  Squaring \(3^{E-2}\) already reaches precision
\(3^E\), proving the second congruence.  Therefore

\[
 C_a(mH)=T e_9(am).                                \tag{TS21}
\]

The finite Wiener--Khinchin identity now gives

\[
 |\widehat f_{E,a}(\ell)|^2
 =\sum_{m=0}^{8}T e_9((a-\ell)m),                  \tag{TS22}
\]

and the final nine-term orthogonality relation proves (TS17).

There is also an exact fixed-harmonic extension.  If
\(s=v_3(h)\), \(E-s\ge4\), \(R=3^s\), and
\(a_0=(h/3^s)\beta10^{n_0}\) reduced modulo \(3^{E-s}\), then the
three-primary sequence over the original length \(T\) repeats \(R\) times.
Its exponent-coordinate transform is supported exactly at

\[
 \ell=Rk,\qquad k\equiv a_0\pmod9,                 \tag{TS23}
\]

and every surviving coefficient has magnitude

\[
                         3\sqrt{RT}.               \tag{TS24}
\]

The case \(s=0\) is (TS17); the general case follows by splitting the
length-\(T\) transform into \(R\) copies of the length-\(T/R\) transform.

## 5. A genuine conditional square-root bound

Return to \(3\nmid h\), and write the exponent-coordinate complementary
weight as

\[
 w(j)=e_C\!\left(h\kappa
    (10^{n_0+j}-16)\right),\qquad0\le j<T.           \tag{TS25}
\]

Let

\[
 \widehat w(\ell)=\sum_{j\bmod T}w(j)e_T(-\ell j).\tag{TS26}
\]

Apart from the harmless constant \(e_{3^E}(-16h\beta)\), the full sum is
\(\sum_j f_{E,a}(j)w(j)\), where
\(a=h\beta10^{n_0}\) and \(a\equiv h\beta\pmod9\).  Fourier inversion and
(TS17) give the exact bound

\[
 \boxed{
 |S_{M,h,n_0}|
 \le {3\over\sqrt T}
 \sum_{\ell\equiv a\ (9)}|\widehat w(-\ell)|.}    \tag{TS27}
\]

Define the restricted normalized Fourier-algebra mass

\[
 \mathcal A_{T,a}(w)={1\over T}
 \sum_{\ell\equiv a\ (9)}|\widehat w(-\ell)|.     \tag{TS28}
\]

Then

\[
                         |S_{M,h,n_0}|
 \le3\sqrt T\,\mathcal A_{T,a}(w).                \tag{TS29}
\]

This supplies a precise sufficient theorem:

\[
 \mathcal A_{T,a}(w)=o(\sqrt T)
 \quad\Longrightarrow\quad S_{M,h,n_0}=o(T).       \tag{TS30}
\]

For example, a bounded linear combination of \(T\)-periodic exponent
characters has bounded \(\mathcal A_{T,a}\) and hence square-root
cancellation.  More generally, a unit-modulus weight with a fixed ordinary
period \(d\) has

\[
 \mathcal A_{T,a}(w)=O_d(\log T),
 \qquad |S_{M,h,n_0}|=O_d(\sqrt T\log T).           \tag{TS31}
\]

To obtain (TS31), expand the \(d\)-periodic weight into its \(d\) exponent
characters.  The normalized Fourier \(\ell^1\)-norm on a length-\(T\)
interval of one fixed rational frequency is \(O(\log T)\), by the standard
geometric-sum bound

\[
 \left|\sum_{j<T}e(\alpha j)\right|
 \le\min\{T,(2\|\alpha\|)^{-1}\}.                 \tag{TS32}
\]

The actual BBP complement has neither a fixed period nor a known bound in
(TS28).  Parseval alone gives only
\(\mathcal A_{T,a}(w)\le\sqrt T/3\), up to the exact support count, which
returns the trivial \(T\)-bound in (TS29).  Thus (TS27) is a positive
conditional result and an exact measurement of the remaining obstruction,
not a completed return estimate.

## 6. Complete-period and primitivity audit for known sum theorems

The word “complete” in the three-primary statement must not be transferred
to the joint CRT orbit.

### 6.1 Full denominator

The complete denominator \(3^EC\) contains powers of 2 and, on the relevant
rows, powers of 5.  Hence

\[
                         (10,3^EC)>1.               \tag{TS33}
\]

The sequence \(10^n\pmod {3^EC}\) is not a multiplicative subgroup of the
unit group.  Complete-subgroup theorems whose base lies in
\((\mathbb Z/q\mathbb Z)^*\) do not apply to this full modulus.  The dyadic
coordinate must remain a synchronized weight.

### 6.2 Unit projection

Let \(Q\) be a product of complete prime-power factors of \(C\), with
\((Q,10)=1\) and \((Q,C/Q)=1\), and project to

\[
                         q_*=3^EQ.                  \tag{TS34}
\]

For \(h=1\), the selected additive coefficient is primitive modulo every
factor of \(q_*\).  Put \(t_Q=\operatorname{ord}_Q(10)\).  The complete joint
subgroup has order

\[
 \operatorname{ord}_{q_*}(10)=\operatorname{lcm}(T,t_Q).     \tag{TS35}
\]

The \(T\)-term three-primary block is a complete joint subgroup if and only
if \(t_Q\mid T\).  That condition is neither a consequence of the
three-primary orbit nor true in general for the actual BBP denominator.

There is a small exact witness.  At the genuine full-grid row \(M=40\),

\[
 E_M=4,\qquad T=9,\qquad L_M-M+1=9,                \tag{TS36}
\]

and the reduced denominator contains \(7^2\).  Direct exact arithmetic gives

\[
 \operatorname{ord}_{49}(10)=42,\qquad
 \operatorname{ord}_{3^4\cdot49}(10)
 =\operatorname{lcm}(9,42)=126.                    \tag{TS37}
\]

Thus the nine-term row is a complete three-primary period but only a short
prefix of the 126-term joint projected subgroup.  This one row is an
`experiment`; it falsifies the unrestricted inference that a complete
three-primary period is automatically a complete joint period.

### 6.3 Size and factor hypotheses

Even if a unit projection happened to satisfy \(t_Q\mid T\), a theorem for a
complete subgroup would still need a size hypothesis.  For the actual
unbounded high-prime product in the frozen large-sieve report,

\[
 Q_M^>=\exp((5+o(1))M),\qquad T=\Theta(M).          \tag{TS38}
\]

If the joint subgroup had only \(T\) elements, then \(T<(3^EQ_M^>)^\delta\)
for every fixed \(\delta>0\) eventually.  Bourgain's arbitrary-modulus
complete-subgroup theorem therefore would not apply in that case.  If the
joint subgroup is much larger, the theorem concerns its entire subgroup,
not the first \(T\) exponents used by the BBP row.

Bourgain--Chang Corollary 4.5 does concern incomplete power prefixes, but its
two relevant assumptions fail on \(3^EQ\):

1. “few prime factors” means a uniform bound on the sum of prime-power
   multiplicities.  The exponent \(E\) is unbounded;
2. for a proper incomplete prefix it explicitly requires
   \(\operatorname{ord}_p(10)>q^\delta\) for every prime \(p\mid q\), while
   \(\operatorname{ord}_3(10)=1\).

The large order \(T\) modulo \(3^E\) does not replace the second assumption;
the source uses projection modulo the prime \(p\) in its incomplete-sum
argument.  Its complete-subgroup Corollary 4.2 and Theorem 4.7 do not convert
the present prefix into a complete subgroup.

## 7. Literature and mathlib audit

### `literature-checked`

Search date: **2026-08-13 UTC**.

The search covered `exponential sums powers modulo prime powers`, `Gauss sums
modulo prime powers`, `multiplicative subgroups arbitrary modulus`, and the
specific Bourgain/Chang complete- versus incomplete-sum hypotheses.

- Jean Bourgain,
  [*Exponential sum estimates over subgroups of
  \(\mathbb Z_q^*\), \(q\) arbitrary*](https://doi.org/10.1007/BF02807410),
  J. Analyse Math. 97 (2005), 317--355, proves cancellation for complete
  multiplicative subgroups of positive-power size.  The open primary summary
  [*Sum--product theorems and exponential sum bounds in residue classes for
  general modulus*](https://doi.org/10.1016/j.crma.2007.01.019), Remark 2,
  states the complete-subgroup hypothesis and bound.  It does not estimate a
  \(T\)-term prefix when the joint order exceeds \(T\).
- Jean Bourgain and Mei-Chu Chang,
  [*Exponential Sum Estimates over Subgroups and Almost Subgroups of
  \(\mathbb Z_q^*\), where \(q\) is Composite with Few Prime
  Factors*](https://doi.org/10.1007/s00039-006-0558-7), Corollaries 4.2 and
  4.5 and Theorem 4.7, was checked directly for Section 6.  The locally pinned
  [PDF](../theory/pi-lacunary-near-return-sparsity/library/t124/bourgain-chang-2006.pdf)
  has SHA-256
  `a4c130e401ff03a5b91fbd20339f06021f26bf871ca2bb375f2ce25e3ee5d1d7`.
- Benji Fisher,
  [*The Stationary-Phase Method for Exponential Sums with Multiplicative
  Characters*](https://doi.org/10.1006/jnth.2002.2790), treats complete
  prime-power sums with multiplicative characters and \(p\)-adic phase
  functions.  It does not supply a bound after multiplication by the changing
  CRT graph weight (TS9).  The elementary autocorrelation proof of (TS17)
  does not depend on this source.
- Bryce Kerr,
  [*Incomplete exponential sums over exponential
  functions*](https://arxiv.org/abs/1302.4170), treats one prime modulus and
  is already used for the local-coordinate bounds in the frozen large-sieve
  report.  Its pinned
  [PDF](../theory/pi-long-lag-block-collision-decay/library/t70/kerr-1302.4170v1.pdf)
  has SHA-256
  `9136dc3965da376942f653b2b06de8d92d7e5e997ee536e1257979698b73e4bd`.
  It does not estimate the unbounded synchronized CRT product.

No primary theorem located turns the nonlinear pulled-back complement in
(TS9) into a complete classical Gauss, Kloosterman, or multiplicative-
character sum with satisfied hypotheses.  This is a bounded applicability
statement, not an exhaustiveness or novelty claim.

The mathlib search found reusable generic infrastructure:

- `Mathlib/Analysis/Fourier/ZMod.lean` contains the discrete Fourier
  transform on `ZMod` and its relation to Dirichlet-character Gauss sums;
- `Mathlib/Analysis/Fourier/FiniteAbelian/Orthogonality.lean` contains finite
  character orthogonality;
- `Mathlib/NumberTheory/DirichletCharacter/GaussSum.lean` contains primitive
  Gauss-sum identities.

It did not find a theorem stating (TS17), the nonlinear permutation (TS10),
or a bound for the BBP-selected coefficient in (TS12).  No formal file is
changed in this branch.

## 8. Exact bounded replay

The companion checker is
[bbp_three_primary_twisted_sum_20260813_check.py](bbp_three_primary_twisted_sum_20260813_check.py),
SHA-256
`7d8a8f7ff85c02b251845ba781d373dbf222a87ba69e0d6f82b1e995b9315e2c`.

It checks the three frozen hashes, replays the exact order, grid, shift, and
autocorrelation congruences for \(4\le E\le12\), performs a small floating
DFT sign check, reconstructs every CRT term of the actual \(M=40\) row, and
checks the \(7^2\) joint-order obstruction.  Its retained output is:

```text
status=PASS
bounded_claim_label=experiment
analytic_claim_label=proof sketch
source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
frozen_three_primary_sha256=5b34ceb3aa2857b9227cce5ac7ae84cafbbac47d2c12adf889c37f11280d6fd7
frozen_large_sieve_sha256=23b3cba4c2b7c5846b4b18748994db8c9e897725612eaf80d08b32b3a97b781d
frozen_t73_sha256=1499b29893a05fe91d64ee468ff320f0f59c23eb07f13220dab64b9fbfe23009
primary_exponent_range=4..12
order_checks=35
grid_bijection_checks=88569
autocorrelation_zero_checks=88488
autocorrelation_nonzero_checks=81
fourier_support_checks=59046
fourier_zero_checks=472368
numerical_dft_sign_checks=2556
actual_depth=40
actual_primary_exponent=4
actual_period=9
actual_row_length=9
actual_exact_crt_checks=9
actual_exact_grid_factor_checks=9
actual_adversarial_saturation_checks=9
actual_seven_exponent=2
actual_seven_order=42
actual_joint_projected_order=126
actual_full_modulus_base_is_unit=false
actual_three_period_is_joint_complete=false
asserts_bbp_complement_fourier_bound=false
asserts_full_phase_cancellation=false
asserts_fixed_sixteen_return=false
asserts_v1=false
```

Run from the repository root with

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_three_primary_twisted_sum_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_three_primary_twisted_sum_20260813_check.py
```

Every bounded row and numerical transform in the replay has label
`experiment`; finite checks are not a proof of any asymptotic estimate.

## 9. Sharp handoff

The complete three-primary grid does isolate the missing statement exactly.
For the row method to gain full-phase cancellation, it is enough to prove

\[
 \boxed{
 \mathcal F_TW_{M,h,n_0}(-h\beta_M)=o(1)}          \tag{TS39}
\]

for every fixed nonzero \(h\) along a suitable unbounded family of complete-
grid rows.  Equivalently, in the original exponent coordinate it is enough
to establish the restricted Fourier-algebra estimate in (TS30), or a direct
bound sharper than (TS27), for the **actual** synchronized dyadic and
odd-cofactor weight.

The new sparse transform (TS17) proves square-root cancellation for
low-Fourier-complexity complements and rules out the idea that the isolated
three-primary phase itself lacks oscillation.  The remaining difficulty is
the growing selected CRT graph.  Current complete-subgroup, incomplete-power,
local-prime, and ordinary orthogonality theorems do not bound it with their
checked hypotheses.  No V1 claim is made.

## 10. Coordination record

This branch registered descendant-area watch
`watch:local:pi-digits:three-primary-twisted-sum-20260813` on
`local:pi-digits` for agent `codex-three-primary-twisted-sum`.  The initial
poll was empty at cursor and delivered sequence 57,289, so no event was
acknowledged.  Observation events are coordination signals only and are not
used as mathematical evidence.
