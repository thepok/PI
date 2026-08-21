# Hutton cross-index phase collapse: exact anti-independence of the CRT factors

Audit date: **2026-08-12 UTC**
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
Provenance: Marcel's immutable local question has no external source URL;
none is invented here. This note continues the existing problem record using
the fields of [`problems/TEMPLATE.md`](../../problems/TEMPLATE.md).

## Outcome and claim status

No proof that every finite decimal word occurs in pi was obtained. The
canonical V1 statement remains a `conjecture`.

This attack decisively falsifies a tempting way to escape the selected-
numerator bottleneck: averaging the changing Hutton CRT factors across many
indices with the same mandatory decimal shift. Put

\[
 H_K=8T_3(2K+2)+4T_7(2K+2),\qquad R_K=4K+3,
\]

and let $b_K=v_5(\operatorname{den}H_K)$. For every $b\ge0$, the exact
transient block

\[
 \mathcal I_b=
 \left\{K:{5^b-1\over4}\le K\le {5^{b+1}-5\over4}\right\}                \tag{1}
\]

contains exactly $5^b$ indices, and $b_K=b$ throughout it. If
$K_b=(5^b-1)/4$, $s\in\mathbb Z_{\ge0}$ is one common post-transient offset, and
$h\in\mathbb Z$, then

\[
 \left|e\!\left(h10^{b+s}H_K\right)
       -e\!\left(h10^{b+s}H_{K_b}\right)\right|
 \le 2\pi|h|10^{b+s}W_{K_b},\qquad K\in\mathcal I_b,                    \tag{2}
\]

where $e(x)=\exp(2\pi ix)$ and the exact Hutton width is

\[
 W_K={8\over(4K+5)3^{4K+5}}+{4\over(4K+5)7^{4K+5}}.                     \tag{3}
\]

Consequently, for every fixed $h\ne0$ and every fixed
$0<\delta<\log_{10}3$, uniformly for

\[
 0\le s\le(\log_{10}3-\delta)5^b,                                       \tag{4}
\]

\[
 \left|{1\over5^b}\sum_{K\in\mathcal I_b}
 e\!\left(h10^{b+s}H_K\right)\right|=1-o(1).                            \tag{5}
\]

Thus the **full** phase collapses to a point (which may depend on $b$ and
$s$), not an equidistributed family.
This remains true through any fixed positive proportion below the earliest
member's linear Hutton horizon.

The failure is even sharper in the CRT split. Let $G_K$ be the T61 product
of eligible upper-half primes and write the post-transient modulus as
$m_K=G_KB_K$. With the canonical additive coordinates $X_{K,s}$ on
$G_K$ and $Y_{K,s}$ on $B_K$, one has exactly

\[
 e(10^{b+s}H_K)=X_{K,s}Y_{K,s}.                                          \tag{6}
\]

Equation (2) therefore implies the pointwise anti-independence law

\[
 \left|Y_{K,s}-e(10^{b+s}H_{K_b})\overline{X_{K,s}}\right|
 \le2\pi10^{b+s}W_{K_b}.                                                  \tag{7}
\]

The complementary coordinate asymptotically conjugates whatever motion the
selected-prime coordinate makes. An isolated $G_K$-factor Weyl estimate,
even if true, cannot survive their product.

More generally, without fixing a transient block, T58 gives at every
transferable pair $(K,s)$ the direct identity-with-error

\[
 \left|Y_{K,s}-e(10^{b_K+s}\pi)\overline{X_{K,s}}\right|
 \le2\pi10^{b_K+s}W_K.                                                     \tag{7a}
\]

Thus the complementary factor contains exactly the selected inverse times
the still-unknown fixed-pi phase, up to the certified bracket error.

Equations (1)--(7a) and the weighted reduction in Section 5 are a `proof
sketch`: the elementary derivations are complete below, but they have not
been registered as Lean declarations. Their bracket and transient inputs are
`machine-checked` in T58 and T63. The exact finite replay is an `experiment`.
Nothing here is a `candidate resolution`.

## 1. Normalized target and ambiguous quantifiers

The target remains

\[
 \forall\ell\ge0\ \forall c<10^\ell\ \exists j\ge0:\quad
 \left\lfloor10^\ell\{10^j\pi\}\right\rfloor=c,                        \tag{V1}
\]

with $c$ padded to length $\ell$, leading zeroes allowed, occurrence
contiguous, and $\ell=0$ vacuous.

Three cross-index claims must not be conflated.

1. Vary $K$ while holding the exact decimal position $j=b+s$ fixed.
   This note proves that the full states collapse exponentially.
2. Vary both $K$ and $s=s(K)$. Then the exact positions $b+s(K)$
   vary, and the family samples different positions of the fixed pi orbit.
3. Average only the selected-prime CRT coordinate. This discards the
   complementary coordinate, whose correlation is exactly (7).

Only the second reading can still contain new cylinder samples, and Section
5 shows precisely what estimate it asks for.

## 2. The exact transient blocks

Every power $5^b$ is $1\pmod4$. Hence both endpoints in (1) are
integers. At the first endpoint,

\[
 R_{K_b}=5^b+2,
\]

and at the last endpoint,

\[
 R=5^{b+1}-2.
\]

It follows that $5^b\le R_K<5^{b+1}$ for every
$K\in\mathcal I_b$. T63 gives the exact identity

\[
 b_K=\lfloor\log_5R_K\rfloor=b.                                          \tag{8}
\]

The cardinality is not asymptotic:

\[
 |\mathcal I_b|
 ={(5^{b+1}-5)-(5^b-1)\over4}+1=5^b.                                    \tag{9}
\]

Thus this is the natural largest cross-$K$ family on which the mandatory
post-transient shift is literally the same integer.  This includes the edge
case $b=0$: then $mathcal I_0=\{0\}$, $R_0=3$, and (9) gives one index.

For completeness, this really is the whole base-ten transient.  Every
summand of $H_K$ has an odd denominator: at odd exponent $r$ it has a
denominator dividing $r3^r7^r$.  A common denominator for their finite sum
is therefore odd, so the reduced denominator $Q_K$ is odd.  After removal
of its exact factor $5^b$, the remaining denominator is coprime to $10$.

## 3. Bracket nesting forces phase collapse

T58 gives

\[
 H_K\le\pi\le H_K+W_K.                                                     \tag{10}
\]

The lower Hutton shadows increase with $K$: the two new exponents are
$r=4K+5$ and $r+2$, and for each base $q\in\{3,7\}$,

\[
 {1\over r q^r}-{1\over(r+2)q^{r+2}}>0.                                  \tag{11}
\]

Therefore, for $K\in\mathcal I_b$,

\[
 0\le H_K-H_{K_b}\le\pi-H_{K_b}\le W_{K_b}.                             \tag{12}
\]

The chord inequality $|e(x)-e(y)|\le2\pi|x-y|$ proves (2). Averaging
and using the reverse triangle inequality gives the fully explicit bound

\[
 \left|{1\over5^b}\sum_{K\in\mathcal I_b}
 e(h10^{b+s}H_K)\right|
 \ge1-2\pi|h|10^{b+s}W_{K_b}.                                             \tag{13}
\]

Here $4K_b+5=5^b+4$, and

\[
 W_{K_b}\le {12\over(5^b+4)3^{5^b+4}}.                                  \tag{14}
\]

Under (4), the logarithm of the error in (13) is at most

\[
 -\delta(\log10)5^b+O_h(b),                                               \tag{15}
\]

which tends to minus infinity exponentially in $b$. This proves (5).
No prime-distribution hypothesis is involved.

There is also a direct word-level consequence. If
$10^{b+s}W_{K_b}<10^{-\ell}$, all the fractional parts
$\{10^{b+s}H_K\}$, $K\in\mathcal I_b$, lie in one circular arc shorter
than a length-$\ell$ decimal cylinder. For the standard half-open decimal
cylinders, such an arc can cross at most one cylinder boundary, so it can
intersect at most two cylinders adjacent in the circular partition.  (If it
wraps through $0$, the last and first cylinders are circularly adjacent;
when $\ell=0$ there is only one cylinder.) Varying $5^b$ rational shadows
at one fixed offset therefore does not create $5^b$ independent word
samples.

## 4. Exact CRT anti-independence

Write $H_K=P_K/Q_K$ in lowest terms. By (8),

\[
 m_K={Q_K\over5^b}=G_KB_K,\qquad (G_K,B_K)=1,qquad (m_K,10)=1,            \tag{16}
\]

and put

\[
 a_K\equiv2^bP_K\pmod {m_K}.
\]

The canonical additive CRT coordinates are

\[
 \alpha_K\equiv a_KB_K^{-1}\pmod {G_K},\qquad
 \beta_K\equiv a_KG_K^{-1}\pmod {B_K}.                                  \tag{17}
\]

Define

\[
 X_{K,s}=e_{G_K}(\alpha_K10^s),\qquad
 Y_{K,s}=e_{B_K}(\beta_K10^s).                                            \tag{18}
\]

Additive CRT and cancellation of $5^b$ give exactly

\[
 X_{K,s}Y_{K,s}
 =e_{m_K}(a_K10^s)
 =e(10^{b+s}H_K),                                                         \tag{19}
\]

which is (6). Multiplying the difference in (2) by
$\overline{X_{K,s}}$ proves (7).

This is stronger than saying that two factors are merely “correlated.” On
the whole range (4), their product approaches one common unit phase
uniformly, so one factor determines the other up to an exponentially small
error. Multiplying (19) by $\overline{X_{K,s}}$ and comparing $H_K$ with pi
through T58 also proves (7a). The fact that $G_K$, $B_K$, and their local
residues all change with $K$ does not weaken either conclusion.

## 5. What a surviving cross-index estimate would have to prove

The same argument works for arbitrary varying offsets. Let
$\mathcal A$ be any finite collection of pairs
$(K,s)\in\mathbb Z_{\ge0}^2$, put
$j(K,s)=b_K+s$, and let

\[
 w_j=\#\{(K,s)\in\mathcal A:j(K,s)=j\}.
\]

For every integer $h$, T58 and the chord inequality give

\[
\begin{aligned}
 &\left|\sum_{(K,s)\in\mathcal A}e(h10^{b_K+s}H_K)
       -\sum_jw_j e(h10^j\pi)\right|\\
 &\hspace{35mm}\le
 2\pi|h|\sum_{(K,s)\in\mathcal A}10^{b_K+s}W_K.                         \tag{20}
\end{aligned}
\]

Thus every transferable cross-$K$ phase average is, up to the explicit
right side, a **weighted Weyl sum of the fixed pi orbit**. For a common
$(b,s)$, all the weight is concentrated at one $j$, producing (5). If
one chooses varying $s(K)$ to avoid this collapse, the minimal new estimate
is a weighted moving-position estimate for

\[
                 e(h10^{j(K)}\pi),                                       \tag{21}
\]

or, equivalently within the error in (20), for the complete product
$X_{K,s(K)}Y_{K,s(K)}$. An estimate for $X$ alone is not a relaxation of
this target because (7) exhibits exact cancellation by $Y$ in the largest
natural fixed-shift families.

For V1 one does not need full Weyl cancellation, but one still needs a
localized cylinder hit by the complete product at a transferable offset.
The earlier `hutton_prefix_sum_attack.md` proves that the assertion that all
words have such Hutton-bracket hits is equivalent to V1. Equation (20) now
shows why cross-index averaging does not change that logical boundary.

## 6. Exact replay and finite falsification

The companion checker is
[`hutton_cross_k_phase_collapse_check.py`](hutton_cross_k_phase_collapse_check.py).
Run it from the repository root:

```text
python3 work/ultrapi-resume/hutton_cross_k_phase_collapse_check.py
```

The 2026-08-12 run reported:

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

The band endpoints, exact denominator shifts, rational bracket diameters,
T61 local residues, and additive-CRT identities use only integers and
`Fraction`. The displayed complex means use floating-point trigonometry and
have only `experiment` status. They illustrate (7): at $b=3,s=0$, the
selected and complementary factor means each have magnitude about $0.016$,
while their product mean has magnitude one to the displayed precision.

## 7. Source and verification boundary

No new external theorem is used. The inputs were already searched and
audited in the following records:

- T58's exact Hutton bracket in
  [`T58T58HuttonRationalShadow.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T58T58HuttonRationalShadow.lean);
- T61's eligible upper-half prime factors in
  [`T61T61HuttonUpperHalfPrimeSurvival.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T61T61HuttonUpperHalfPrimeSurvival.lean);
- T63's exact five-adic transient in
  [`T63T63HuttonFiveAdicTransient.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T63T63HuttonFiveAdicTransient.lean);
- the dated literature and mathlib searches in
  [`hutton_prefix_sum_attack.md`](hutton_prefix_sum_attack.md) and
  [`hutton_global_crt_attack.md`](hutton_global_crt_attack.md).

The new conclusion is deliberately negative but exact: cross-$K$ variation
inside one mandatory-shift block produces many changing local descriptions
of essentially one fixed archimedean phase. A successful continuation must
control varying decimal positions of the **joint** selected/complementary
state; it cannot obtain a cylinder hit from selected-prime phase cancellation
or CRT-factor independence.
