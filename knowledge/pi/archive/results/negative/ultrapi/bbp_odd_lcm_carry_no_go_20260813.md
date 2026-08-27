# Odd-LCM BBP carry attack: exact cancellation and a bounded-gap no-go

Audit date: **2026-08-13 UTC**

Target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt)

Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

Parent report:
[bbp_fixed_period_carry_attack_20260813.md](bbp_fixed_period_carry_attack_20260813.md),
SHA-256
`bdc77060ef42a15f8985d70b70cf9777c36070713c940a18e89e05b149734d55`.

## Outcome and claim status

No positive carry-density theorem and no proof that every finite decimal word
occurs in pi was obtained.  Canonical V1 remains a `conjecture`.

This branch resolves the proposed odd-prime/LCM route in two directions.  The
infinite deductions have status `proof sketch`; the exact replay has status
`experiment`.

1. The sevenfold rational BBP carry has an exact scalar recurrence.  After
   normalization, the large new LCM multiplier cancels from the expanding
   term and survives only through the seven-term rational forcing.  Modulo
   every new LCM prime power, the next centered numerator is independent of
   the carry.  Hence a new-prime valuation cannot distinguish zero carry from
   nonzero carry.
2. This is not merely a weak estimate.  Five consecutive exact zero carries
   occur while each row acquires a nontrivial, squarefree odd LCM quotient of
   31--106 bits and the forcing is a unit modulo that entire quotient.
3. A uniform bounded-gap conclusion is the wrong target: V1 itself implies,
   for every fixed period (P), arbitrarily late carry-free blocks of every
   finite length.  The same is true for the eventually exact sevenfold
   rational carries.  Positive lower density is compatible with these
   unbounded gaps.
4. An (O_P(\log n)) zero-run bound would require a polynomial lower bound
   for (\|(10^P-1)10^n\pi\|_{\mathbb T}).  An (o(n)) bound is equivalent
   to a restricted denominator exponent-one statement.  The published
   irrationality measure supplies only an (O_P(n)) bound.

These results sharply prune the search: neither fresh odd LCM primes nor a
bounded-gap theorem can prove the required positive density.  No result here
has status `machine-checked`, `candidate resolution`, or `verified resolution`.

## 1. Exact target and quantifiers

Canonical V1 asks whether every finite word over
({0,1,\ldots,9}), including words with leading zeroes, occurs as one
contiguous block in the decimal expansion of pi.  It does not ask about one
fixed word, an infinite subsequence, or a finite computed prefix.

Fix a period (P\geq1) and put

\[
 q=q_P=10^P-1.
\]

For the true orbit define

\[
 z_n=\left\lfloor q10^n\pi+\frac12\right\rfloor,
 \qquad e_n=q10^n\pi-z_n,
 \qquad \gamma_n=z_{n+1}-10z_n.                    \tag{1}
\]

Pi is irrational, so no value in (1) lies on a half-integer boundary.  Thus
(-1/2<e_n<1/2) and

\[
 e_{n+1}=10e_n-\gamma_n,
 \qquad \gamma_n\in\{-5,-4,\ldots,5\}.             \tag{2}
\]

The unresolved sufficient condition isolated in the parent report is a
positive lower density of nonzero carries for every fixed (P), along one
common sequence of cutoffs.  Infinitely many nonzero carries or a weak bound
on their gaps is not enough.

## 2. The exact sevenfold rational recurrence

Combine the four BBP poles as

\[
 a_k={c_k\over d_k},\qquad
 c_k=120k^2+151k+47,
 \quad d_k=(2k+1)(4k+3)(8k+1)(8k+5),               \tag{3}
\]

and write

\[
 B_m=\sum_{k=0}^m{a_k\over16^k},\quad
 L_m=\mathop{\rm lcm}(d_0,\ldots,d_m),\quad
 A_m=\sum_{k=0}^m c_k16^{m-k}{L_m\over d_k}.        \tag{4}
\]

Then (B_m=A_m/(16^mL_m)).  At a seven-step transition put

\[
\begin{aligned}
 R_n&={L_{7n+7}\over L_{7n}},\\
 H_n&=\sum_{k=7n+1}^{7n+7}
       c_k16^{7n+7-k}{L_{7n+7}\over d_k},\\
 \alpha_n&=2^{27}R_n,\\
 D_n&=2^{27n}L_{7n},\\
 U_n&=q5^nA_{7n},\\
 J_n&=q5^{n+1}H_n.                                  \tag{5}
\end{aligned}
\]

Directly splitting old and new terms in (4) gives

\[
 A_{7n+7}=16^7R_nA_{7n}+H_n.                        \tag{6}
\]

Consequently

\[
 D_{n+1}=\alpha_nD_n,
 \qquad U_{n+1}=10\alpha_nU_n+J_n.                 \tag{7}
\]

The rational approximation in the parent report is exactly

\[
 {U_n\over D_n}=q10^nB_{7n}.                        \tag{8}
\]

Let (\widehat z_n=\lfloor U_n/D_n+1/2\rfloor),
(S_n=U_n-D_n\widehat z_n), and
(\widehat\gamma_n=\widehat z_{n+1}-10\widehat z_n).  Then

\[
 \boxed{S_{n+1}=10\alpha_nS_n+J_n
                    -\widehat\gamma_nD_{n+1}.}     \tag{9}
\]

This is an equality in integers, not a congruence or an asymptotic formula.

### 2.1 What normalization does to the new LCM factor

Set (\widehat e_n=S_n/D_n) and
(\delta_n=J_n/D_{n+1}).  Translation invariance of nearest-integer
rounding turns (9) into

\[
\boxed{
 \widehat\gamma_n
  =\left\lfloor10\widehat e_n+\delta_n+\frac12\right\rfloor,
 \qquad
 \widehat e_{n+1}
  =10\widehat e_n+\delta_n-\widehat\gamma_n.}       \tag{10}
\]

Moreover, cancellation of (L_{7n+7}) gives

\[
 \boxed{
 \delta_n
 =q10^{n+1}\bigl(B_{7n+7}-B_{7n}\bigr).}           \tag{11}
\]

Thus (R_n) is absent from the expanding coefficient in (10).  Its
arithmetic is still encoded in the seven new rational coefficients in
(11), so it would be incorrect to say that the new primes disappear from
the problem.  What disappears is the hoped-for large-modulus amplification:
the carry decision remains one nearest-integer comparison for a scalar real
number.

### 2.2 The new-prime congruence cannot see the carry

Because (R_n\mid\alpha_n) and (R_n\mid D_{n+1}), (9) implies

\[
 \boxed{S_{n+1}\equiv J_n\pmod {R_n}.}              \tag{12}
\]

More strongly, replacing (\widehat\gamma_n) in the right side of (9) by
*any* integer leaves the same residue modulo (R_n).  Therefore for every
prime (p) and exponent (a\leq v_p(R_n)),

\[
 S_{n+1}\equiv J_n\pmod {p^a}                       \tag{13}
\]

is independent of whether the actual carry is zero.  If
(\gcd(J_n,R_n)=1), (12) proves that the next centered numerator is a unit
at every new prime, but it still gives no carry information.  This is the
exact obstruction to the proposed valuation argument.

## 3. Exact finite falsification of new-prime forcing

For (P=1), the exact rational stream contains

\[
 \widehat\gamma_{761}=\widehat\gamma_{762}
 =\widehat\gamma_{763}=\widehat\gamma_{764}
 =\widehat\gamma_{765}=0.                           \tag{14}
\]

Every one of these transitions has substantial fresh odd LCM growth:

| (n) | exact factorization of (R_n) | bits | (gcd(J_n,R_n)) |
|---:|---|---:|---:|
| 761 | (21319\cdot21323\cdot42641\cdot42649\cdot42677) | 75 | 1 |
| 762 | (21347\cdot42689\cdot42697\cdot42701\cdot42709) | 76 | 1 |
| 763 | (21379\cdot21383\cdot21391\cdot42737\cdot42773) | 74 | 1 |
| 764 | (21407\cdot21419\cdot42793\cdot42797\cdot42821\cdot42829\cdot42841) | 106 | 1 |
| 765 | (42853\cdot42901) | 31 | 1 |

All displayed factors are prime, their products equal the exact LCM
quotients, and (12) makes (S_{n+1}) a unit modulo the whole quotient.
Nevertheless the carry vanishes.  Conversely, (R_{438}=R_{727}=1) while
(\widehat\gamma_{438}=1) and (\widehat\gamma_{727}=-4).  These finite
rows do not prove an asymptotic law; they decisively falsify the local rule
"fresh prime implies nonzero carry" and its unit-residue strengthening.

The independently pinned decimal source also certifies the true (P=1)
window

\[
 (\gamma_{710098},\ldots,\gamma_{710105})
 =(-4,0,0,0,0,0,0,5).                              \tag{15}
\]

This is an `experiment`, not a proof of unbounded gaps.  The next section
gives the exact conditional theorem that does imply unbounded gaps under V1.

## 4. V1 forces arbitrarily long zero-carry blocks

For (H\geq1), (2) gives the elementary equivalence

\[
 \boxed{
 \gamma_n=\cdots=\gamma_{n+H-1}=0
 \quad\Longleftrightarrow\quad
 \|q10^n\pi\|_{\mathbb T}<{1\over2\,10^H}.}        \tag{16}
\]

Indeed, a zero block makes (e_{n+t}=10^te_n) for (0\leq t\leq H),
so the last centered error gives the right side.  Conversely, the right side
keeps (10^te_n) strictly inside the nearest-integer cell for every
(t\leq H), forcing
(z_{n+t}=10^tz_n) and hence every displayed carry to vanish.

Now assume V1.  The decimal orbit

\[
 \mathcal O=\{10^n\pi\bmod1:n\geq0\}               \tag{17}
\]

is dense in the circle: occurrences of all finite words make the orbit meet
every decimal cylinder, and decimal cylinders form a topological base.  In
fact every tail of (17) is dense.  If (T(x)=10x\bmod1), the tail beginning
at (N) is (T^N(\mathcal O)); continuity and surjectivity give

\[
 \mathbb T=T^N(\overline{\mathcal O})
 \subseteq\overline{T^N(\mathcal O)}.               \tag{18}
\]

Multiplication by the fixed integer (q) is also a continuous surjection of
the circle, so every tail of

\[
 \{q10^n\pi\bmod1:n\geq0\}                          \tag{19}
\]

is dense.  Equivalently, the original decimal orbit comes arbitrarily close
to one of the (q)-torsion points (k/q); proximity to zero is sufficient
but is not required.  Given arbitrary (N) and (H), density of the tail
selects (n\geq N) with the right side of (16).  Therefore

\[
 \boxed{
 \text{V1}\Longrightarrow
 \text{for every fixed (P,H,N), some (n\geq N) begins an
 (H)-term zero-carry block}.}                      \tag{20}
\]

For every fixed (P), the parent report proves from the sevenfold BBP tail
and the published bound (mu(\pi)<8) that
(\widehat\gamma_{n,P}=\gamma_{n,P}) for all sufficiently large (n).
Choose (n) in (20) beyond that onset.  Thus (20) also holds for the exact
rational carries (\widehat\gamma_{n,P}).

It follows that a uniform bound on gaps between nonzero carries is
incompatible with V1 and cannot be a route to proving V1.  This does **not**
undermine the required positive-density target: a set can have positive
lower density and unbounded complementary intervals.  For example, deleting
([2^j,2^j+j]) from the nonnegative integers leaves density one but creates
gaps of unbounded length.

## 5. The exact quantitative stopping point

Let (h_P(n)) be the maximal number of consecutive true zero carries
starting at (n).  It is finite because otherwise (1) would make pi
rational.  Since equality at a boundary in (16) would also make pi rational,
(16) yields the exact identity

\[
 \boxed{
 h_P(n)=\left\lfloor
 -\log_{10}\bigl(2\|(10^P-1)10^n\pi\|_{\mathbb T}\bigr)
 \right\rfloor.}                                   \tag{21}
\]

Take (M=888/125=7.104), strictly above the published upper bound for
(mu(\pi)).  For fixed (P), the irrationality-measure quantifiers imply,
for all sufficiently large (n),

\[
 \|q10^n\pi\|_{\mathbb T}
 > (q10^n)^{1-M}.                                   \tag{22}
\]

Equations (21)--(22) give only

\[
 h_P(n)<(M-1)n+(M-1)\log_{10}q-\log_{10}2,          \tag{23}
\]

whose slope is (M-1=763/125).  This recovers the linear gap scale behind
the parent's logarithmic count of nonzero carries.

For fixed (P), an estimate

\[
 h_P(n)\leq C\log_{10}(n+2)+C_0                     \tag{24}
\]

is equivalent, up to changing positive constants, to

\[
 \|q10^n\pi\|_{\mathbb T}\geq c(n+2)^{-C}.         \tag{25}
\]

In rational-approximation language, with (Q_n=q10^n) and nearest numerator
(z_n), (25) is

\[
 \left|\pi-{z_n\over Q_n}\right|
 \geq {c\over Q_n(n+2)^C},                         \tag{26}
\]

a denominator-(Q^{-1}) lower bound with only a polylogarithmic loss in
(Q).  Similarly,

\[
 h_P(n)=o(n)
 \quad\Longleftrightarrow\quad
 -\log_{10}\|q10^n\pi\|_{\mathbb T}=o(n),          \tag{27}
\]

which says that the nearest approximants on the restricted denominator grid
(q10^n) have logarithmic approximation exponent one.  Neither (25) nor
(27) follows from the finite global irrationality measure, which gives the
much smaller lower bound (22).

Even (24), if obtained, would generally force only on the order of
(N/\log N) nonzero carries below (N), not the (\Omega(N)) count needed
for positive lower density.  Thus logarithmic or sublinear gaps are valid
intermediate Diophantine targets, but they do not close the carry-density
criterion.

## 6. Exact replay, source boundary, and handoff

The companion
[bbp_odd_lcm_carry_no_go_20260813_check.py](bbp_odd_lcm_carry_no_go_20260813_check.py)
has SHA-256
`12d9ffef815f60b39d8f4d2f8c946bab10c1e29be94d25f19dfb1039ee15a905`.
It pins five inputs, checks 800 exact sevenfold recurrences and 8,800
candidate-independent LCM congruences, verifies every factorization and unit
claim in the table, and certifies (15) from decimal enclosures.  Run:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_odd_lcm_carry_no_go_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_odd_lcm_carry_no_go_20260813_check.py
```

The retained run reported `status: PASS`.  The checker explicitly sets the
bounded-gap, logarithmic-gap, positive-density, and V1 flags to false.

The BBP formula, irrationality-measure quantifiers, sevenfold stability, and
source applicability are inherited only from the pinned parent report and
its independent audit.  This note makes no novelty or exhaustive-literature
claim.  No mathlib infrastructure or Lean declaration was added, so there is
no new theorem to register in `audit/AxiomAudit.lean` and no formal gate to
run for this branch.

The useful next target is therefore not "show every block of (C) steps has
a carry."  It is the strictly weaker but still unresolved average statement

\[
 \#\{0\leq n<N:\widehat\gamma_{n,P}\ne0\}=\Omega_P(N),
\]

or an independent route to the empirical-measure alternative.  Fresh odd
LCM factors alone cannot supply that statement through valuations, and the
known irrationality measure reaches only the linear gap bound (23).
