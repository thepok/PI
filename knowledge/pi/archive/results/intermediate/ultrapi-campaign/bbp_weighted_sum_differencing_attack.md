# BBP weighted quotient sum: Weyl collapse, nonterminating differencing, and selector barriers

Audit date: **2026-08-12 UTC**

Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)

Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

Parent report:
[`bbp_actual_odd_quotient_attack.md`](bbp_actual_odd_quotient_attack.md),
SHA-256
`d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc`.

## Outcome and claim status

No estimate of the parent's equation (43), fixed-sixteen return, or proof
that every finite decimal word occurs in pi was obtained.  Canonical V1
remains a `conjecture`.

The direct attack does give four exact boundary results, recorded as a
`proof sketch`.

1. The two factors in the weighted quotient sum multiply exactly to the
   ordinary decimal Weyl block for the rational BBP truncation.  Uniformly
   over the whole proportional row, its normalized value differs by at most
   $2\pi|h|/[15(M+1)^2]$ from the corresponding block of pi.
2. Every finite additive or multiplicative van der Corput difference stays
   in the same lacunary family.  A lag $r$ replaces $h$ by
   $h(10^r-1)$; after several lags the multiplier is
   $h\prod_j(10^{r_j}-1)$.  No polynomial-style terminal constant appears.
   This general geometric-phase identity was already machine-checked in
   T13; its application here is not a novelty claim.
3. Additive CRT gives an exact character product, but the index follows one
   diagonal cyclic orbit rather than a Cartesian product of local orbits.
   Consequently the sum does not factor into local sums, and standard
   complete-orbit bounds are outside the required logarithmic-in-modulus
   range.
4. A sharp selector theorem fixes the **entire actual odd quotient**
   $c_M/R_M$ and changes only the dyadic coordinate.  An alternative reduced
   numerator at the same denominator can make the full proportional-row
   average have magnitude tending to one, while its rational value remains
   within $2^{-M}$ of the actual BBP truncation.  Thus no bound using the odd
   CRT data—even all of it—can work without the actual dyadic carry.  A
   second construction shows that the known high-prime coordinates and the
   stated cofactor size/support restrictions also admit resonant rows.

The selector constructions deliberately do **not** satisfy the actual
four-pole carry recurrence.  They are barriers to information-discarding
proofs, not counterexamples for pi.  The companion checker is an
`experiment`; the dated source search is `literature-checked`.  The cited
T13 and T26 dependencies are `machine-checked`, but no new theorem in this
note is.  Nothing here is a `candidate resolution` or a `verified
resolution`.

## 1. Exact target and the complete phase

Retain the parent's notation

\[
 A_n=\frac{10^n-16}{16},\qquad
 T_M=\lfloor\lambda M\rfloor-M+1,\qquad
 \lambda=\log_{10}16,                               \tag{1}
\]

and put $L_M=\lfloor\lambda M\rfloor$.  Since $M\ge5$, every $A_n$ in
the row $M\le n\le L_M$ is an integer.  The useful elementary identities
are

\[
 A_n+1=\frac{10^n}{16},\qquad
 A_{n+1}=10A_n+9,\qquad 3\mid A_n.                 \tag{2}
\]

The parent decomposes

\[
 16B_M=y_M+\frac{c_M}{R_M},qquad
 \frac{c_M}{R_M}\equiv
 \Xi_M+\frac{\eta_M}{C_M}\pmod1                  \tag{3}
\]

and defines $\kappa_M=y_M+\Xi_M$.  Its weighted sum is

\[
 \mathcal S_{M,h}=\sum_{n=M}^{L_M}
 e(hA_n\kappa_M)
 e\!\left(\frac{hA_n\eta_M}{C_M}\right).          \tag{4}
\]

Equations (1) and (3) collapse the product before any estimate is made:

\[
\boxed{
 \mathcal S_{M,h}
 =\sum_{n=M}^{L_M}e\!\left(h(10^n-16)B_M\right).}  \tag{5}
\]

Thus the explicit high-prime factor and the remaining cofactor factor are
not two averages.  Their product is one character evaluated on the decimal
orbit of the selected rational truncation.

## 2. Uniform transfer to the actual pi block

The positive four-pole coefficient satisfies $a(k)<1/k^2$ for $k\ge1$.
Therefore

\[
 0<\pi-B_M
 \le \frac{16^{-M}}{15(M+1)^2}.                   \tag{6}
\]

For every exponent in the proportional row,
$10^n\le10^{\lambda M}=16^M$, so

\[
 0\le(10^n-16)(\pi-B_M)
 \le\frac1{15(M+1)^2}.                             \tag{7}
\]

Define the actual decimal block

\[
 \mathcal W_{M,h}=\sum_{n=M}^{L_M}e(h10^n\pi).     \tag{8}
\]

The chord inequality and (5)--(7) give the explicit normalized comparison

\[
\boxed{
 \left|
 \frac{\mathcal S_{M,h}}{T_M}
 -e(-16h\pi)\frac{\mathcal W_{M,h}}{T_M}
 \right|
 \le\frac{2\pi|h|}{15(M+1)^2}.}                   \tag{9}
\]

Consequently, along any common unbounded sequence of depths and for every
fixed integer $h$,

\[
 \frac{\mathcal S_{M,h}}{T_M}\longrightarrow0
 \quad\Longleftrightarrow\quad
 \frac{\mathcal W_{M,h}}{T_M}\longrightarrow0.   \tag{10}
\]

This does not prove either limit.  It says that the remaining BBP weighted
sum is exactly as hard, at block-Fourier scale, as a proportional block of
the actual decimal orbit of pi.

There is a useful quantifier boundary.  If (10) holds for all nonzero $h$
and for **every** $M\to\infty$, rather than merely along one subsequence,
then pi is normal to base 10.  Indeed, global Weyl cancellation immediately
implies proportional-block cancellation by subtraction.  Conversely, put
$P_h(N)=\sum_{n<N}e(h10^n\pi)$.  The block hypothesis gives

\[
 P_h(L_M+1)-P_h(M)=o(M).                            \tag{11}
\]

For any large $N$, taking $M=\lceil(N-1)/\lambda\rceil$ makes
$L_M+1$ equal to $N$ or $N+1$.  Iterating (11) down a geometric sequence
and summing its errors proves $P_h(N)=o(N)$.  Weyl's criterion then gives
normality.  The parent's condition (43) only asks for a common unbounded
subsequence, so it does not assert normality, but it is still much stronger
than one cylinder hit.

## 3. Exact van der Corput hierarchy

For a function $f$ on the integers write

\[
 \Delta_r f(n)=f(n+r)-f(n).
\]

Starting with

\[
 f_{M,h}(n)=h(10^n-16)B_M,                          \tag{12}
\]

one difference gives

\[
 \Delta_r f_{M,h}(n)=h(10^r-1)10^nB_M.            \tag{13}
\]

Induction yields, for every $k\ge1$ and positive lags
$r_1,\ldots,r_k$,

\[
\boxed{
 \Delta_{r_k}\cdots\Delta_{r_1}f_{M,h}(n)
 =h10^nB_M\prod_{j=1}^k(10^{r_j}-1).}              \tag{14}
\]

The repository already contains the general machine-checked geometric-phase
version as
[`IteratedLagResonance.iteratedDifference_geometricPhase`](../../TheoryLib/PiLacunaryNearReturnSparsity/T13IteratedLagResonance.lean).
Equation (14) is its shifted rational specialization.

At the first correlation level, if
$z_n=e(h(10^n-16)B_M)$ and $H_r=h(10^r-1)$, then

\[
\begin{aligned}
 \sum_{n=M}^{L_M-r}z_{n+r}\overline{z_n}
 &=\sum_{n=M}^{L_M-r}e(H_r10^nB_M)\\
 &=e(16H_rB_M)
   \sum_{n=M}^{L_M-r}e(H_r(10^n-16)B_M).           \tag{15}
\end{aligned}
\]

Thus a van der Corput step returns a shortened copy of the same missing sum
at the promoted frequency $H_r$.  Iteration only multiplies the frequency
by further factors $10^s-1$.

This hierarchy also fails to terminate through an accidental dyadic
annihilation.  Write

\[
 B_M=\frac{P_M}{2^{K_M}R_M},\qquad
 K_M=4M-v_2(M+1),                                  \tag{16}
\]

with $P_M,R_M$ odd.  Every factor $10^r-1$ is odd.  For fixed $h\ne0$ and
$n\le L_M$, the two-adic denominator left in (14) has exponent

\[
 K_M-n-v_2(h)\ge4M-v_2(M+1)-L_M-v_2(h)\longrightarrow\infty. \tag{17}
\]

The same calculation after one more unit shift proves that the derivative
character is not even constant on two consecutive surviving indices for all
large $M$.  Polynomial Weyl differencing succeeds because degree falls;
here the lacunary factor $10^n$ survives at every finite depth.  A standard
van der Corput inequality is valid, but its correlation hypotheses are
again (10) at larger fixed frequencies.  There is no simpler base case.

## 4. What additive CRT does and does not factor

Let $D_M=2^{K_M-4}$, write $y_M=w_M/D_M$, and set
$e_m(x)=e(x/m)$.  The parent's additive CRT
identity gives the exact character product

\[
\boxed{
 e(hA_n16B_M)
 =e_{D_M}(hA_nw_M)
  \prod_{p\in\mathcal Q_M^\star}
       e_p(hA_n\widehat\gamma_{M,p})
  e_{C_M}(hA_n\eta_M).}                            \tag{18}
\]

This is useful pointwise, but summing over $n$ does not turn the right side
into a product of sums.  The exponent follows the single diagonal orbit

\[
 n\longmapsto
 (10^n\bmod p)_{p\in\mathcal Q_M^\star},           \tag{19}
\]

not independent local indices.  On the odd squarefree product its period is
an lcm of local orders, not their Cartesian product.  The dyadic and
5-primary parts are additionally nonunit for base 10.

Even granting square-root bounds for every relevant twisted **complete**
sum modulo the high product would not reach the row length.  That product
has logarithm $(6+o(1))M$, so its square-root scale is
$\exp((3+o(1))M)$, whereas $T_M\asymp M$.  Completion followed by the
triangle inequality is therefore worse than the original trivial bound.
Applying an unweighted bound at one prime also does not control (18),
because all remaining factors form a synchronized unit weight.

## 5. A full-odd-coordinate dyadic selector theorem

The preceding limitation can be made exact.  This is the strongest new
obstruction in this branch.

Fix a depth $M\ge5$, retain the **actual** odd denominator and quotient
$R_M,c_M/R_M$, and put

\[
 r_M=v_2(M+1),\quad
 D_M=2^{4M-r_M-4},\quad
 Q_M=2^{3M-r_M}.                                   \tag{20}
\]

As an alternative odd dyadic coordinate $w$ varies, the starting decimal
seed of

\[
 \theta(w)=\frac w{D_M}+\frac{c_M}{R_M}            \tag{21}
\]

is

\[
 \frac{10^M\theta(w)}{16}
 \equiv \frac{5^Mw}{Q_M}
       +\frac{10^Mc_M}{16R_M}\pmod1.               \tag{22}
\]

Multiplication by $5^M$ permutes the odd residues modulo $Q_M$.  Those odd
grid points have spacing $2/Q_M$, so there is an odd residue class
$w'_M\pmod {Q_M}$ for which

\[
 \left\|
 \frac{10^M\theta(w'_M)}{16}-\frac19
 \right\|_{\mathbb T}\le\frac1{Q_M}.              \tag{23}
\]

Since $Q_M\mid D_M$, choose a representative $0\le w'_M<D_M$ in this
class no farther than $Q_M$ from the actual coordinate $w_M$.  Define

\[
 P'_M=R_Mw'_M+D_Mc_M,\qquad
 B'_M=\frac{P'_M}{16D_MR_M}.                        \tag{24}
\]

Both $w'_M$ and $P'_M$ are odd, and
$P'_M\equiv D_Mc_M\pmod {R_M}$, so

\[
 (P'_M,2R_M)=1,\qquad
 16B'_M=\frac{w'_M}{D_M}+\frac{c_M}{R_M}.           \tag{25}
\]

The entire odd quotient and hence every odd CRT coordinate—including the
cofactor coordinate—are exactly unchanged.  Also

\[
 |B'_M-B_M|\le\frac{Q_M}{16D_M}=2^{-M}.            \tag{26}
\]

Let $n=M+t\le L_M$.  The point $1/9$ is fixed by multiplication by 10,
and (23) gives

\[
 \left\|\frac{10^n\theta(w'_M)}{16}-\frac19\right\|_{\mathbb T}
 \le\frac{10^t}{Q_M}
 \le\frac{2^{r_M}}{5^M}
 \le\frac{M+1}{5^M}.                              \tag{27}
\]

Since
$A_n\theta=10^n\theta/16-\theta$, all summands lie near one common unit
phase.  For every fixed integer $h$,

\[
\boxed{
 \left|
 \frac1{T_M}\sum_{n=M}^{L_M}e(hA_n16B'_M)
 -e\!\left(h\left(\frac19-16B'_M\right)\right)
 \right|
 \le\frac{2\pi|h|(M+1)}{5^M}.}                    \tag{28}
\]

In particular, the magnitude of the alternative row average tends to one,
not zero.

Equation (28) is not a statement about the actual $w_M$.  It proves the
precise negative result that the full odd quotient, its prime coordinates,
the exact denominator, reducedness, and even convergence
$|B'_M-B_M|\to0$ do not force cancellation uniformly in the dyadic
coordinate.  Any successful use of the odd-prime localization must retain
the selected carry (15) from the parent report.

## 6. A coarse-data separator even when the cofactor is tiny

A complementary construction shows why the upper bounds
$P^+(C_M)=O(M/\log M)$ and $\log C_M=o(M)$ cannot replace the selected
cofactor residue.

Take any squarefree product $S_M$ of primes greater than 3, with nonzero
prescribed additive coordinates $\gamma_{M,p}$, and let

\[
 \Xi_M=\sum_{p\mid S_M}\frac{\widehat\gamma_{M,p}}p.
\]

Choose

\[
 C_M=3^{a_M},\qquad
 a_M=\min\{a:3^a\ge(M+1)^3\}.                      \tag{29}
\]

Then $P^+(C_M)=3$, $\log C_M=O(\log M)$, and for large $M$ its exponent
even obeys the parent's fixed-prime allowance
$a_M\le4\lfloor\log_3(8M+5)\rfloor$.

The reduced residues modulo 6 have cyclic gaps at most four.  Because
$D_MC_M$ is divisible by 6, there are an odd $w_M$ and a unit
$\eta_M\bmod C_M$ such that

\[
 \left\|
 \Xi_M+\frac{w_M}{D_M}+\frac{\eta_M}{C_M}-\frac13
 \right\|_{\mathbb T}\le\frac2{D_MC_M}.           \tag{30}
\]

CRT reconstructs a numerator $c_M$ coprime to $S_MC_M$ with exactly the
prescribed high-prime coordinates and cofactor coordinate $\eta_M$.  Since
$3\mid A_n$ by (2), (30) implies

\[
 \left|
 \frac1{T_M}\sum_{n=M}^{L_M}
 e\!\left(hA_n\left(
 \Xi_M+\frac{w_M}{D_M}+\frac{\eta_M}{C_M}
 \right)\right)-1
 \right|
 \le\frac{4\pi|h|}{(M+1)^2}.                      \tag{31}
\]

This separator may use the actual high-prime coordinate list, but it varies
both unresolved selectors and does not obey the four-pole carry.  Its scope
is only to falsify a uniform theorem based on the coordinate list plus the
cofactor size, support, and prime-power bounds.

## 7. Exact replay

The companion
[`bbp_weighted_sum_differencing_check.py`](bbp_weighted_sum_differencing_check.py)
has SHA-256
`70a4ca42b1bd2c6ec212587662ab667b8c1940a3a95d94b03a1f054ba71066bc`.
It imports neither parent checker.  It uses integers and `Fraction` for all
structural assertions; floating-point complex arithmetic appears only in
explicitly labeled finite diagnostics and redundant chord-bound checks.

Run from the repository root:

```bash
python -m py_compile \
  work/ultrapi-resume/bbp_weighted_sum_differencing_check.py
python work/ultrapi-resume/bbp_weighted_sum_differencing_check.py
```

The retained run reported:

```text
status: PASS
claim_label: experiment
weighted-sum collapse checks: 75
finite-tail transfer checks: 75
iterated-difference checks: 1200
correlation-promotion checks: 1200
dyadic-nontermination checks: 726
actual CRT checks: 162
full-odd-coordinate dyadic-selector checks: 1497
coarse structural-separator checks: 7524
asserts_weighted_sum_bound: false
asserts_fourier_limit: false
asserts_fixed_return: false
asserts_v1: false
```

At depths 48, 64, 96, and 128, the alternative full-odd-coordinate rows
had normalized magnitudes equal to one to displayed floating precision,
with rigorously checked phase-error bounds.  These finite values are an
`experiment`; the infinite estimate is (28), not an extrapolation from the
diagnostic.

## 8. Literature and repository applicability audit

Search date: **2026-08-12 UTC**.

- The general nonterminating geometric-phase identity is already
  `machine-checked` in
  [`T13IteratedLagResonance.lean`](../../TheoryLib/PiLacunaryNearReturnSparsity/T13IteratedLagResonance.lean),
  SHA-256
  `14ae452f34068dd78877054e231c58af02c2563cd755f0ee4edc0ff0ebeeda13`.
  The deterministic van der Corput infrastructure in T66 likewise leaves a
  shifted-frequency premise; it does not estimate that premise at pi.
- [`T26WeylCancellationV1.lean`](../../TheoryLib/PiDigits/T26WeylCancellationV1.lean),
  SHA-256
  `3825d0dcb5bd4d22ffa3cd8853db1bbf79c2ad1faa4ff0f1db96dbf7efc11871`,
  machine-checks that global Weyl cancellation implies V1 and explicitly
  records that this is stronger than orbit density.
- Lagarias,
  [*On the Normality of Arithmetical Constants*](https://arxiv.org/abs/math/0101055v2),
  Theorem 3.1, supplies the general perturbed-radix shadow relation and
  emphasizes that arbitrary perturbation representations do not prove
  normality.  Equation (9) is the sharper summable-tail instance needed here.
- Konyagin--Shparlinski,
  [*On the Consecutive Powers of a Primitive Root: Gaps and Exponential
  Sums*](https://doi.org/10.1112/S0025579311002117), treats a primitive root
  modulo one prime.  Equation (18) has a changing composite modulus,
  nonunit primary factors, and a synchronized weight from every other
  coordinate.
- Kurlberg,
  [*Bounds on Exponential Sums over Small Multiplicative Subgroups*](https://arxiv.org/abs/0705.4573),
  surveys complete subgroup bounds; its cited composite-modulus results use
  a bounded number of prime divisors.  Here the high product has an
  unbounded number and the required interval is only $O(M)$.
- di Benedetto--Garaev--García--González-Sánchez--Shparlinski--Trujillo,
  [*New Estimates for Exponential Sums over Multiplicative Subgroups and
  Intervals in Prime Fields*](https://arxiv.org/abs/2003.06165), obtains
  nontrivial results once subgroup and interval sizes occupy positive-power
  ranges in a prime field.  It does not estimate the one selected diagonal
  composite character in (18).
- Bhakta--Shparlinski,
  [*Exponential Sums with Sparse Polynomials and Distribution of the Power
  Generator*](https://arxiv.org/abs/2412.07989), treats complete sparse
  polynomial sums and power-generator distribution in ranges such as
  $N\ge p^{1-\rho+\varepsilon}$.  The present length is logarithmic in the
  full modulus and carries the selected BBP coefficient.

No checked primary source supplies (43) in this setting.  This is a bounded
applicability statement, not a claim that the literature is exhaustive.

## 9. Sharp handoff

The remaining weighted quotient sum has not become a new tractable
power-generator problem.  It is the ordinary proportional decimal Weyl
block of pi up to the explicit error (9).  Finite differencing is closed on
the same family, and CRT exposes a diagonal product rather than independent
local averages.

The selector theorems identify exactly what cannot be discarded:

\[
\boxed{
 \text{all odd CRT data without the selected dyadic carry can resonate,}
 \quad
 \text{coarse cofactor bounds without its selected residue can resonate.}}
\]

A viable continuation must use the simultaneous, actual pair
$(w_M,\eta_M)$ through the four-pole cross-depth recurrence, or abandon the
all-frequency Weyl target for a genuinely weaker cylinder-hitting argument.
No such estimate was proved here, so V1 remains a `conjecture`.
