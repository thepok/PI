# Independent audit: CF36 Gowers obstruction and cube persistence

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
This is Marcel's immutable local question and has no external source URL; none
is invented here.

## 1. Frozen scope and verdict

The independently audited artifacts are:

| artifact | SHA-256 |
|---|---|
| [primary report](bbp_cf36_gowers_cube_persistence_20260813.md) | `3bd9a948945570e975defd7bd2297338da0068f9c82eb027be84364a66bb528e` |
| [primary checker](bbp_cf36_gowers_cube_persistence_20260813_check.py) | `24adf41ff8197d354ea8a5569dbb227f521346e96287006d013b77e6fb3fdea9` |

The four mathematical dependencies were also hash-checked:

| frozen dependency | SHA-256 |
|---|---|
| [three-primary twisted-sum report](bbp_three_primary_twisted_sum_20260813.md) | `0a7e6015782afdfa407242fe3e191cfffec414d7c9215ec8854a439c2fb08a12` |
| [three-primary decimation report](bbp_three_primary_decimation_20260813.md) | `29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0` |
| [complement-Fourier report](bbp_complement_fourier_attack_20260813.md) | `eccb19ffdd7a931cb9de1efb4ab1136ba3f8fb543a84ab00c3e320fd16f2316a` |
| [high-prime compression report](bbp_high_prime_phase_compression_20260813.md) | `47f56886b769a36f5f397cad567579838d455f59b75af8ca458a8000dfb7c564` |

**Audit verdict: PASS WITH SCOPE CLARIFICATIONS.** I found no fatal defect in
the elementary algebra supporting the report's four `proof sketch`
conclusions. The result is a useful obstruction and persistence analysis, but
it gives no bound for CF36, no fixed-sixteen return, and no proof of canonical
V1. The disjoint checker below has label `experiment`; no claim is promoted to
`machine-checked`, `candidate resolution`, or `verified resolution`.

The scope clarifications are substantive:

1. The complement $W=\overline f$ is artificial. It proves that marginal
   fixed-order Gowers uniformity cannot control the selected pairing; it says
   neither that the BBP complement equals $\overline f$ nor that its selected
   correlation is large.
2. The exact unit-coefficient second moment is an average over all
   $a\in(\mathbb Z/3^e\mathbb Z)^\times$. The BBP coefficient is one coherent
   three-adic lift and is not licensed to behave like a fresh random sample at
   each depth.
3. Cube persistence is termwise. It does not prevent cancellation between the
   many terms created by expanding a differenced block sum and therefore is not
   a lower bound for that block sum.
4. The third-difference conclusion is for a dissociated legal lag triple, in
   particular $(1,2,4)$ when $H>7$, not for every third-lag triple. The
   primary report states this restriction correctly.
5. The asymptotic high-prime mass in the cube conclusion inherits the pinned
   $(5+o(1))M$ theorem from the frozen high-prime dependency. The new report
   correctly does not relabel that inherited input or its new deductions as
   formal Lean results.

## 2. Normalized target and quantifiers

The exact target remains the `conjecture`

\[
 \forall P\ge1\ \forall k\in\{0,\ldots,10^P-1\}\ \exists n\ge0:\quad
 \left\lfloor10^P\{10^n\pi\}\right\rfloor=k.       \tag{IA1}
\]

The word represented by $k$ has exactly $P$ decimal digits, so leading
zeroes are retained. The quantifier asks for one contiguous occurrence of each
finite word. It does not ask for infinitely many occurrences, positive
frequency, normality, or an occurrence of every infinite digit string. The
audited branch concerns only a stronger Fourier estimate on selected BBP
endpoint rows; failure to prove that estimate is not evidence against (IA1).

## 3. Exact Gowers calculation

Put

\[
 q=3^e,\qquad T=3^{e-2},\qquad
 f_{e,a}(x)=e_q(a10^x),\qquad 3\nmid a.             \tag{IA2}
\]

Because $10$ generates the subgroup $1+9\mathbb Z/3^e\mathbb Z$, the
map $x\mapsto r_x=(10^x-1)/9$ permutes $\mathbb Z/T\mathbb Z$. Hence,
for every integer $c$,

\[
 \mathbb E_{x\bmod T}e_q(c10^x)
 =e_q(c)\mathbb E_{r\bmod T}e_T(cr),               \tag{IA3}
\]

which vanishes unless $T\mid c$. An $s$-fold multiplicative derivative of
$f_{e,a}$ has coefficient, up to an irrelevant sign,

\[
                 a\prod_{i=1}^s(10^{h_i}-1).       \tag{IA4}
\]

For $d=e-2$, a nonzero $h\bmod3^d$ with $v_3(h)=j$ has
$v_3(10^h-1)=2+j$, while the zero lag occurs with probability $1/T$.
There are $2\cdot3^{d-j-1}$ residues of exact finite valuation $j<d$.
After excluding zero lags, support of the $x$-average requires

\[
                     j_1+\cdots+j_s\ge d-2s.       \tag{IA5}
\]

For $d\ge2s$, summing the resulting geometric composition tail gives

\[
 O_s(T^{-1})+
 {2^s\over3^s}\sum_{r\ge d-2s}
 {r+s-1\choose s-1}3^{-r}
 =O_s\!\left({e^{s-1}\over T}\right).             \tag{IA6}
\]

The finitely many smaller depths are absorbed into the implied constant.
Taking absolute values only after the exact $x$-average shows that (IA6) is
an upper bound for $\|f_{e,a}\|_{U^s}^{2^s}$. Thus the fixed-order decay
claimed in the primary report follows. This does not assert cancellation among
the supported cubes.

For $s=2$, the pinned exact Fourier support has $T/9$ coefficients and
normalized squared magnitude $9/T$. Consequently

\[
 {T\over9}\left({9\over T}\right)^2={9\over T},   \tag{IA7}
\]

which rederives the exact $U^2$ fourth power. For $s=3$, union-bounding the
three zero-lag events by $3/T$ and using (IA5) with $R=e-8\ge0$ gives the
reported explicit upper bound

\[
 \|f_{e,a}\|_{U^3}^{8}
 \le {3\over T}+{2(R+2)^2\over3^{R+1}}
 ={3+486(e-6)^2\over T}.                           \tag{IA8}
\]

The disjoint replay used a dynamic convolution of the exact valuation counts,
rather than the primary checker's nested enumeration, and confirmed (IA8) for
nine even exponents through $e=24$.

## 4. The conjugate obstruction is exact

Let $W_{e,a}=\overline{f_{e,a}}$. Complex conjugation preserves every
$U^s$-norm, but

\[
             T^{-1}\sum_{j<T}f_{e,a}(j)W_{e,a}(j)=1.          \tag{IA9}
\]

With $H=T/9$, the exact lift

\[
                 10^{mH}\equiv1+mT\pmod {3^e}               \tag{IA10}
\]

implies $f(u+mH)=f(u)e_9(am)$. Therefore the primary block operator satisfies

\[
 \sum_{m=0}^8e_9(am)W(u+mH)=9\overline{f(u)}.      \tag{IA11}
\]

This checks the sign in the report: the $e_9(am)$ factor cancels the
$e_9(-am)$ contributed by $\overline f$. The independent checker tested
(IA10)--(IA11) for all six unit classes modulo nine on each even row through
$e=12$. The proof itself is the displayed congruence, not the finite test.

Equations (IA9)--(IA11) are a decisive information-scope counterexample:
small marginal $U^s(W)$ alone cannot imply the desired relative-correlation
bound. They are not a counterexample to CF36 for the actual BBP complement.

## 5. Exact unit-average second moment

For

\[
 S_a(W)=\sum_{j\bmod T}e_q(a10^j)W(j),
 \qquad a\in(\mathbb Z/q\mathbb Z)^\times,          \tag{IA12}
\]

expand the square and average over unit $a$. The prime-power Ramanujan sum,
normalized by $\varphi(q)=6T$, is $1$ when $q\mid n$, is $-1/2$ when
$3^{e-1}\mid n$ but $q\nmid n$, and is zero otherwise. On exponent
differences $10^j-10^k$, the two off-diagonal nonzero cases are exactly
$j-k\equiv T/3,2T/3\pmod T$. Thus

\[
 {1\over\varphi(q)}\sum_{3\nmid a}|S_a(W)|^2
 =T-\operatorname {Re}\sum_{j\bmod T}
 W(j+T/3)\overline{W(j)}\le2T.                    \tag{IA13}
\]

No independence or randomness hypothesis enters (IA13). Since the total
square mass is at most $(6T)(2T)=12T^2$, the number of unit coefficients with
$|S_a(W)|\ge\eta T$ is at most

\[
                              {12\over\eta^2}.     \tag{IA14}
\]

This confirms both the constant and its depth independence. The disjoint
checker classified all 66,429 lags through $e=12$ and exhausted all $2^9$
unit-modulus sign weights on the first row using exact `Fraction` arithmetic.

For $W=\overline{f_{e,a_0}}$, the shifted product is the constant
$e_3(-a_0)$. Its real part is $-1/2$, so the right side of (IA13) is
$3T/2$ while $S_{a_0}(W)=T$. This confirms that one exceptional selected
unit is fully compatible with the average theorem.

## 6. Coefficient nesting

At a pre-drop endpoint, let

\[
 M_e^-={5(3^e-1)\over8}-1,
 \qquad U_e=3^eB_{M_e^-},
 \qquad a_e\equiv hU_e10^{M_e^-}\pmod {3^e},       \tag{IA15}
\]

with fixed $3\nmid h$. The pinned decimation result gives
$U_e\equiv U_{e-2}\pmod {3^{e-2}}$, and direct subtraction gives

\[
 M_e^--M_{e-2}^-=5\cdot3^{e-2},
 \qquad \operatorname {ord}_{3^{e-2}}(10)=3^{e-4}.             \tag{IA16}
\]

The order in (IA16) divides the endpoint difference, so

\[
                         a_e\equiv a_{e-2}\pmod {3^{e-2}}.    \tag{IA17}
\]

Raising $\overline{e_{3^e}(a_e10^u)}$ to the ninth power reduces the modulus
to $3^{e-2}$; (IA17) then gives the reported compatibility with the previous
depth. The finite endpoint residue table was replayed for four unit harmonics.

The logical conclusion is exactly the report's: the selected coefficient is a
coherent path through nine lifts. Equation (IA14) supplies no theorem that this
particular path eventually avoids the bounded exceptional set.

## 7. Second- and third-cube nondegeneracy

After expanding an $s$-fold multiplicative difference of the nine-block
inner sum, a term has integer coefficient

\[
 C_{\mathbf m,\mathbf d}
 =\sum_{\omega\in\{0,1\}^s}(-1)^{|\omega|}
 10^{m_\omega H+\omega\cdot\mathbf d},            \tag{IA18}
\]

and the constant part of $A_n=10^n/16-1$ cancels. Also

\[
 |C_{\mathbf m,\mathbf d}|
 \le2^s10^{8H+d_1+\cdots+d_s}
 <2^s10^{(8+s)H}.                                  \tag{IA19}
\]

For $s=2$, the even-parity exponent residues modulo $H$ are
$\{0,d_1+d_2\}$, while the odd-parity residues are $\{d_1,d_2\}$.
They are disjoint whenever $0<d_1,d_2<H$: an intersection would force
$d_1$ or $d_2$ to be $0\pmod H$. Equality between the positive and
negative sums in (IA18) would require equality of their two exponent
multisets, because every decimal-place multiplicity is at most two and no
carry is possible. Disjoint residues exclude that equality, so every
second-cube coefficient is nonzero.

For $s=3$, each side has four powers of ten, so the same no-carry argument
remains valid. At $(d_1,d_2,d_3)=(1,2,4)$, the eight subset sums are
$0,1,\ldots,7$, hence distinct modulo every $H>7$. Every full exponent is
therefore distinct across the cube vertices, independent of the eight block
indices, and $C_{\mathbf m,\mathbf d}\ne0$. This argument deliberately does
not extend automatically to arbitrary higher $s$, where decimal
multiplicities can reach or exceed ten; the primary report makes no such
extension.

The independent replay exhaustively checked all 419,904 second-cube block
assignments on $H=9$, checked the universal third-cube residue argument for
$H=9,27,81,243$, and reconstructed 4,096 distinct third-cube integer samples.
These bounded checks have label `experiment`.

## 8. Retained high-prime mass and dyadic depth

For fixed nonzero $h$ and sufficiently large $M>|h|$, a selected
high-prime local coordinate is killed in a nondegenerate term only when its
prime divides $C_{\mathbf m,\mathbf d}$. Because the selected product is
squarefree, the product of killed primes divides $|C|$. Combining the pinned
$(5+o(1))M$ logarithmic mass with (IA19) and

\[
                            H={8M+13\over405}       \tag{IA20}
\]

gives

\[
 \log Q_{M,s}^{\rm surv}
 \ge\left(5-{8(8+s)\log10\over405}+o(1)\right)M.  \tag{IA21}
\]

For $s=2,3$, the independently recomputed constants are respectively

\[
              4.545168376692534\ldots,
              \qquad4.499685214361788\ldots.      \tag{IA22}
\]

This argument applies to the original or recombined high-prime coordinate;
it must not be read as an estimate of one arbitrarily separated summand of a
CRT decomposition. The pinned denominator theorem supplies a unit local
coordinate at every selected prime, which is the fact needed for (IA21).

For the dyadic factor, $w_M$ is odd and
$K_M=4M-v_2(M+1)$. After removing the common $2^{M+u}$ and the factors in
$hC$, the remaining denominator exponent is bounded below by

\[
 K_M-M-u-v_2(h)-v_2(C).                            \tag{IA23}
\]

Since $v_2(C)\le\log_2|C|$, equations (IA19)--(IA20) yield

\[
 L_{M,s}\ge
 \left(3-{8(1+(8+s)\log_2 10)\over405}+o(1)\right)M.         \tag{IA24}
\]

The constants for $s=2,3$ are

\[
               2.324063586195089\ldots,
               \qquad2.258445253456573\ldots.     \tag{IA25}
\]

Thus the claimed termwise persistence and its constants are correct within
the pinned input scope. Equations (IA21)--(IA25) say nothing about the sign or
size of the sum of those terms.

## 9. Disjoint replay and hygiene

The [independent checker](bbp_cf36_gowers_cube_persistence_20260813_independent_check.py),
SHA-256
`ddb579322dd7e9238024e313947bc94ae0bf9d3ce33af28cdf7859ea73370bdf`,
imports no primary checker and uses no floating-point phase evaluation. It
uses exact integers, `Fraction`, and high-precision `Decimal` only for printing
the four logarithmic constants.

Run from the repository root:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_cf36_gowers_cube_persistence_20260813_independent_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_cf36_gowers_cube_persistence_20260813_independent_check.py
```

The retained output was:

```text
asserts_cf36_bound=False
asserts_fixed_return=False
asserts_v1=False
dyadic_constant_s2=2.32406358619508891893919616207616984180447774952600876798918
dyadic_constant_s3=2.25844525345657311947509108692576213462690083312058495343008
endpoint_scale_checks=40
external_links=2
gowers_bound_checks=9
high_constant_s2=4.54516837669253418587298934228457003306644908866592138745021
high_constant_s3=4.49968521436178760446028827651302703637309399753251352619523
hygiene_file_checks=7
moment_weight_checks=512
nesting_checks=1012
nine_block_resonance_checks=4914
primary_permutation_checks=66429
ramanujan_lag_checks=66429
relative_links=6
second_multiset_checks=419904
second_residue_checks=64
second_size_checks=419904
third_residue_pair_checks=112
third_sample_checks=4096
u2_frequency_checks=66429
exact_record_sha256=3fbfbe3ce0508db971bfa77e8e5476b1d7565d797bb36b6ef1683b8f7c9178e8
status=PASS
```

The primary checker was also compiled and rerun independently. It reproduced
its retained record SHA-256
`12253c483c206d11e741f6656b1f3dad61042ac0bef312fd697c28d04ce4d2fb`
and `status=PASS`.

All seven pinned local files were free of forbidden C0 control bytes. All six
relative links in the primary report resolved. Its two DOI links were kept
external and were directly checked in the literature pass below. Claim labels
match the repository vocabulary, and the report explicitly retains false flags
for a CF36 bound, fixed return, and V1. No Lean, `ultrapi.md`, verified-track,
or audit-gate file was edited by this branch.

## 10. Mathlib and literature applicability

### literature-checked

Direct-check date: **2026-08-13 UTC**.

- A local search of `.lake/packages/mathlib/Mathlib`, `TheoryLib`,
  `ErdosLab`, and `audit` found no Gowers definition or theorem. It did find
  the existing deterministic van der Corput core in
  `TheoryLib/PiLongLagBlockCollisionDecay/T66T66DeterministicShiftedFrequencyVdC.lean`.
  The primary report was therefore right not to claim reused formal Gowers
  infrastructure.
- W. T. Gowers, [*A New Proof of Szemerédi's
  Theorem*](https://doi.org/10.1007/s00039-001-0332-9), GAFA 11 (2001),
  465--588, is correctly identified as a source for higher-order uniformity.
- B. Green and T. Tao, [*Linear Equations in
  Primes*](https://annals.math.princeton.edu/wp-content/uploads/annals-v171-n3-p08-p.pdf),
  Annals of Mathematics 171 (2010), 1753--1850, directly lists Gowers norm
  theory in Appendix B and the generalized von Neumann theorem in Appendix C.
  Proposition 7.1 controls specified multilinear systems of affine-linear
  forms; it does not assert that two adversarially coupled functions with small
  marginal Gowers norms have small pointwise inner product.

The exact counterexample (IA9)--(IA11) already settles that non-applicability
without relying on an interpretation of either paper. No external theorem is
used to establish (IA3)--(IA25), and this bounded search is not a novelty
claim.

## 11. Coordination record and final claim boundary

This audit registered descendant-area watch
`ultrapi-cf36-gowers-independent-20260813` on `local:pi-digits` for agent
`codex-ultrapi-cf36-gowers-independent`. Its initial poll was empty at cursor
and delivered sequence 57,435. Its final pre-verdict poll was also empty at
the same cursor and delivered sequence, so no event was acknowledged.
Observation events are coordination signals only and were not used as
mathematical evidence.

The positive retained result is the exact unit-average theorem (IA13)--(IA14):
only $O_\eta(1)$ unit primary coefficients can be macroscopically correlated
with any fixed unit-modulus complement. The obstruction is equally exact: the
actual BBP coefficient follows one coherent lift path, and marginal Gowers
uniformity plus ninth-root compatibility does not force that path out of the
exceptional set. Second and selected third differences retain exponentially
large moduli term by term, but may still cancel after summation.

Therefore the only claim status retained for the new mathematical deductions
is `proof sketch`; the bounded checker remains `experiment`, the applicability
search is `literature-checked`, and canonical V1 remains a `conjecture`.
