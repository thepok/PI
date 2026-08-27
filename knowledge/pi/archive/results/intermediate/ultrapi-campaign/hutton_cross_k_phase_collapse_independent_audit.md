# Independent audit: Hutton cross-index phase collapse

Audit date: **2026-08-12 UTC**
Canonical target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)
Audit scope:
[`hutton_cross_k_phase_collapse.md`](hutton_cross_k_phase_collapse.md) and
[`hutton_cross_k_phase_collapse_check.py`](hutton_cross_k_phase_collapse_check.py)

## Verdict

**PASS at the corrected `proof sketch` level.**  The transient blocks,
uniform Hutton-bracket collapse, full-phase mean lower bound, additive CRT
product, selected/complementary anti-independence, and weighted reduction to
the fixed-pi orbit all re-derive exactly.  The replay passes after three
auditability corrections and one wording clarification:

1. the advertised edge block $b=0$ is now included in the exact replay;
2. the report now proves that every reduced Hutton denominator is odd, so
   removal of $5^b$ really leaves a modulus coprime to $10$ and $b$ is the
   complete base-ten transient;
3. the decimal-cylinder statement now specifies half-open cells and circular
   adjacency, including wraparound through zero; and
4. the common offsets are explicitly nonnegative integers, while the
   collapsing point is allowed to depend on $(b,s)$.

No proof of V1 follows.  The canonical every-word statement remains a
`conjecture`.  The new cross-index conclusions are not Lean declarations and
remain a `proof sketch`; the finite replay is an `experiment`.  Nothing here
is a `candidate resolution` or a `verified resolution`.

## Audited pins

- canonical target SHA-256:
  `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
- corrected report SHA-256:
  `af405be8543128655f36fb1a2c315feded5048ee15ec9ee4235ecc0734020f39`
- corrected checker SHA-256:
  `9a9adb130538826382bc2c0c69d952d4f33a36d12cc7b4905acf076ee955b8d1`

No new external theorem is used.  The bracket and exact five-adic valuation
inputs are the already registered T58 and T63 `machine-checked` results.  The
upper-half denominator multiplicity used to define the selected CRT product
is the T61 `machine-checked` result.  The phase and CRT deductions audited
here are elementary but have not themselves been formalized.

## 1. Transient endpoints, cardinality, and the $b=0$ edge

Since $5^b\equiv1\pmod4$, both

\[
 K_b={5^b-1\over4},\qquad L_b={5^{b+1}-5\over4}
\]

are integers.  Direct substitution into $R_K=4K+3$ gives

\[
 R_{K_b}=5^b+2,\qquad R_{L_b}=5^{b+1}-2.
\]

Thus $5^b\le R_K<5^{b+1}$ throughout $K_b\le K\le L_b$, and T63 gives
$v_5(\operatorname{den}H_K)=b$.  The exact number of indices is

\[
 L_b-K_b+1
 ={5^{b+1}-5-5^b+1\over4}+1=5^b.
\]

This remains valid at $b=0$: $K_0=L_0=0$, $R_0=3$, and the block contains
one index.  The checker previously began at $b=1$; it now replays
$b=0,1,2,3$.  In particular it computes

\[
 H_0={87112\over27783},\qquad v_5(27783)=0.
\]

At odd exponent $r$, a combined Hutton summand has denominator dividing
$r3^r7^r$, which is odd.  A finite common denominator is therefore odd, and
so is the reduced denominator $Q_K$.  Writing $Q_K=5^b m_K$, T63 now gives

\[
 (m_K,10)=1.
\]

Moreover no shift smaller than $b$ removes the remaining factor of $5$.
Hence $b$ is the exact base-ten preperiod, not merely its five-primary part.

## 2. Bracket diameter and uniform offset range

Going from $K$ to $K+1$ adds, for each $q\in\{3,7\}$, the pair with
$r=4K+5$,

\[
 {1\over rq^r}-{1\over(r+2)q^{r+2}}>0.
\]

After multiplication by the positive Hutton coefficients, this proves that
$H_K$ increases.  T58 gives $H_K\le\pi\le H_K+W_K$, so for every
$K\in[K_b,L_b]$,

\[
 0\le H_K-H_{K_b}\le\pi-H_{K_b}\le W_{K_b}.
\]

The chord bound $|e(x)-e(y)|\le2\pi|x-y|$ therefore gives, for integer $h$,

\[
 |e(h10^{b+s}H_K)-e(h10^{b+s}H_{K_b})|
 \le 2\pi|h|10^{b+s}W_{K_b}.
\]

Here $4K_b+5=5^b+4$ and

\[
 W_{K_b}
 ={8\over(5^b+4)3^{5^b+4}}
  +{4\over(5^b+4)7^{5^b+4}}
 \le {12\over(5^b+4)3^{5^b+4}}.
\]

For $0\le s\le(\log_{10}3-\delta)5^b$, the natural logarithm of the
right-hand side is bounded by

\[
 -\delta(\log 10)5^b+O_h(b).
\]

This tends to $-\infty$ uniformly in the indicated integer offsets.  The
range and exponent in the report are therefore correct; the $10^b$ transient
cost contributes only the lower-order $O(b)$ term.

## 3. Mean lower bound and decimal-cell endpoint nuance

Let $z_K=e(h10^{b+s}H_K)$ and $z_0=z_{K_b}$.  With
$E_b=2\pi|h|10^{b+s}W_{K_b}$,

\[
 \left|{1\over5^b}\sum_Kz_K-z_0\right|\le E_b,
 \qquad
 \left|{1\over5^b}\sum_Kz_K\right|\ge1-E_b.
\]

The matching upper bound is $1$, so the modulus of the mean is $1-o(1)$
uniformly over the stated range.  This is collapse around a unit phase that
may change with $b$ and $s$; it is not convergence to one fixed point across
different blocks.

For the word-level statement, all lifted values $10^{b+s}H_K$ lie in a real
interval of length at most $10^{b+s}W_{K_b}$.  If that length is strictly
less than $d=10^{-\ell}$, its projection to the circle is an arc shorter
than the spacing between two consecutive decimal-cell boundaries.  It can
therefore cross at most one boundary and meet at most two half-open cells.
If it crosses zero, cells $10^\ell-1$ and $0$ are adjacent in the circular
partition.  Strict inequality eliminates the only two-boundary endpoint
case; for $\ell=0$ the partition has only one cell.  The corrected claim is
exact with these conventions.

## 4. Additive CRT product and anti-independence

Write $H_K=P_K/Q_K$ in lowest terms and $Q_K=5^b m_K$.  For the squarefree
product $G_K$ of T61-eligible upper-half primes, T61 gives exact denominator
multiplicity one at each selected prime.  Consequently

\[
 B_K=m_K/G_K\in\mathbb Z,qquad (G_K,B_K)=1.
\]

Let $a_K\equiv2^bP_K\pmod {m_K}$ and define

\[
 \alpha_K\equiv a_KB_K^{-1}\pmod {G_K},\qquad
 \beta_K\equiv a_KG_K^{-1}\pmod {B_K}.
\]

Then $\alpha_KB_K+\beta_KG_K\equiv a_K$ modulo both coprime factors and
hence modulo $m_K$.  Thus

\[
 {\alpha_K\over G_K}+{\beta_K\over B_K}
 \equiv {a_K\over m_K}\pmod1.
\]

After multiplication by $10^s$ and exponentiation,

\[
 X_{K,s}Y_{K,s}=e_{m_K}(a_K10^s)
 =e(10^{b+s}H_K),
\]

because

\[
 10^{b+s}{P_K\over5^bm_K}={2^bP_K10^s\over m_K}.
\]

Multiplying the full-phase difference by the unit
$\overline{X_{K,s}}$ proves the report's anti-independence inequality
without any probabilistic assumption.  Replacing the block reference phase
by $e(10^{b+s}\pi)$ and applying T58 gives the pointwise version (7a).
Changing moduli with $K$ does not affect this termwise identity.

The formulas also extend to a trivial factor of modulus one under the usual
one-element-ring convention.  The finite CRT experiment deliberately uses
only blocks where $G_K>1$, so it never relies on an implementation-specific
inverse modulo one.

## 5. Weighted reduction to fixed-pi Weyl sums

For any finite set of nonnegative integer pairs $(K,s)$ and integer $h$, T58
and the chord inequality give termwise

\[
 |e(h10^{b_K+s}H_K)-e(h10^{b_K+s}\pi)|
 \le2\pi|h|10^{b_K+s}W_K.
\]

Summation and regrouping equal positions $j=b_K+s$ gives exactly

\[
 \left|\sum_{(K,s)}e(h10^{b_K+s}H_K)
 -\sum_jw_je(h10^j\pi)\right|
 \le2\pi|h|\sum_{(K,s)}10^{b_K+s}W_K.
\]

Thus varying $K$ at a common $(b,s)$ repeats one fixed decimal position,
while choosing varying offsets merely creates a weighted sum over positions
of the original pi orbit.  This is an exact reduction, not a Weyl estimate:
it supplies no cancellation or cylinder hit by itself.  Estimates for the
selected factor alone are insufficient because the complementary factor is
its conjugate times the full fixed-pi phase up to the bracket error.

## 6. Replay

The corrected command

```text
python3 work/ultrapi-resume/hutton_cross_k_phase_collapse_check.py
```

reports:

```text
source sha256: 2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
exact band/transient/diameter/odd-denominator assertions: 624
exact selected-prime/additive-CRT assertions: 5217
finite phase experiment: b s #K |mean G| |mean B| |mean product| log10(epsilon)
  2  0  25 0.223519053529 0.223519053529 1.000000000000 -11.597645
  2  8  25 0.091221967301 0.091218356584 0.999999998996 -3.597645
  3  0 125 0.015948430001 0.015948430001 1.000000000000 -58.957962
  3 43 125 0.072900806656 0.072900806656 1.000000000000 -15.957962
all exact checks passed; complex means are experiments only
```

The integer and `Fraction` assertions verify the finite endpoint,
valuation, odd-denominator, local-residue, and additive-CRT calculations.
The displayed complex magnitudes use floating-point trigonometry and retain
only `experiment` status.  They are consistent with the proved bound but are
not evidence for V1.
