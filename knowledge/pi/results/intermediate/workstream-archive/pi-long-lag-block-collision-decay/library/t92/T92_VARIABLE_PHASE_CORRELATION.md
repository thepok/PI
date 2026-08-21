# T92: Variable-phase sibling of the centered critical-band correlation condition

Claim label: `proof sketch`.

The T87 and T90 interfaces cited below are `machine-checked`. The new
variable-phase moment calculations and the finite obstruction in this note
are rigorous prose and therefore retain the label `proof sketch`.

## 1. Provenance and scope

- Canonical local statement: `CANONICAL_STATEMENT.txt`.
- Canonical SHA-256:
  `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`.
- Original external source URL: none. The local statement records that the
  system formulated the question on 2026-07-23.
- Sibling status: this note concerns only the residual sparse-Fourier sibling
  A12. It does not concern the canonical collision count directly.
- Established mathematical inputs: only the kernel-checked T87 and T90
  interfaces listed in Section 3. Definitions occurring literally in their
  theorem types, such as `translatedCanonicalBlocks`, are unfolded only to
  read those interfaces; no theorem from another item is used as an
  additional premise.
- External literature: none is used. All Fourier integral identities needed
  below are proved directly in finite form. No novelty claim is made.

This note makes no assertion about the phase `pi`, C1, C2, C3, decimal
disjunctivity, or the canonical collision count. In particular, the
positive-measure obstruction below is an obstruction for a Lebesgue-random
variable phase, not evidence about `pi`.

## 2. Normalized statement and quantifier audit

Let

\[
  \lambda(A)=\operatorname{Leb}(A\cap[0,1))
\]

be Lebesgue measure restricted to the half-open unit interval. Thus
\(\lambda([0,1))=1\). All almost-everywhere assertions in this note refer to
this probability measure.

The phrase "replace pi only in the Fourier phases" has the following exact
meaning. T90's fixed-phase term

\[
  \cos(2\pi^2 h d)
\]

contains one \(\pi\) from the Fourier kernel and one from evaluating the
phase at `alpha = pi`. Replacing only the phase input gives

\[
  \cos(2\pi\alpha h d),
\]

not \(\cos(2\alpha^2 h d)\) and not \(\cos(2\pi^2\alpha h d)\).

The variable-phase sibling is required to retain this quantifier order:

\[
  \lambda\text{-a.e. }\alpha\in[0,1),\quad
  \forall Q_0,m,N\in\mathbb N,
\]

subject to

\[
  1\le m,\qquad 1\le N,\qquad
  10^m\le N^2\le 2\cdot10^m.
  \tag{CB}
\]

There is no adjustable constant in T90's `CORR_pi`; the coefficient of the
critical normalization is literally one. The universally quantified \(Q_0\)
is retained even though T87's exclusion audit makes the resulting formula
independent of \(Q_0\).

Two possible readings of "refutes it almost everywhere" must not be
confused:

1. To refute the assertion "the condition holds for almost every alpha," it
   suffices to exhibit a positive-measure failure set.
2. To prove "the condition fails for almost every alpha" would require a
   full-measure failure set.

Section 8 proves the first statement and does not assert the second.

## 3. Machine-checked input map

The following facts are used as established input.

From T87:

- `not_arithmeticExcluded_eight_one`: for \(m\ge1\), \(r\ge m\), and every
  \(Q_0,n\), the arithmetic exclusion at \((\mu,c)=(8,1)\) is false.
- `blockRecordDomain_both_orientations_eight_one`: each surviving core has
  exactly the two Boolean orientations, with signed frequencies \(-d\) and
  \(+d\), and with weak left and strict right block endpoints.
- `inclusiveFrequencies_card_exact`: the inclusive frequency set has exact
  cardinality \(10^m\). The literal set `Finset.Icc 1 (10 ^ m)` is displayed
  in T87's fully unfolded formulas and T90's block-energy formula.
- `recordDiagonal_exact_formula_literal`: the record diagonal uses every
  canonical block, both orientations, every inclusive frequency, and the
  literal square-root width.
- `recordDiagonal_normalized_critical_bounds_literal`: the positive band
  (CB), its endpoint inclusions, and the stated normalization are explicit.

From T90:

- `mem_blockCoreDomain_literal`: the lower-dimensional core domain has the
  exact lag, start, and endpoint inequalities used below.
- `blockRecordDomain_eight_one_eq_orientations` and
  `blockCoreDomain_orientation_exclusion_audit`: the record domain is exactly
  two signed orientations of the core domain, with no hidden exclusion.
- `two_orientations_phase_eq_cosine`: at the fixed phase, the two signs
  combine to twice a cosine. Its proof exposes the Fourier kernel and hence
  determines the variable-phase replacement used here.
- `blockSquaredEnergy_eight_one_pi_eq_coreSum` and
  `widthWeightedSquareFunction_eight_one_pi_eq_coreSum`: after the two
  orientations are combined, squaring gives the literal factor four.
- `recordDiagonal_eq_coreCard`: the exact diagonal is twice the core
  cardinality at each of the \(10^m\) frequencies.
- `full_four_orientation_alignment_defect_identity_literal`: the centered
  observable is the triangle majorant minus the alignment defect, retaining
  all four ordered sign choices produced by squaring.
- `criticalNormalization_eq_T29_half`: the displayed normalization is
  exactly T29's \(s=1/2\) normalization.

No claim from an unverified note is used as a premise.

## 4. Literal finite domains

Fix positive integers \(m,N\) satisfying (CB), and put

\[
  H:=10^m.
\]

Let \(\mathcal B_N\) be T29's ordered list
`translatedCanonicalBlocks N`, namely the canonical dyadic partition of
\([1,N)\). A block \(B\) has natural-number endpoints

\[
  [a_B,b_B)=[B.\mathrm{start},B.\mathrm{finish})
\]

and literal width

\[
  w_B:=\sqrt{b_B^2-a_B^2}.
  \tag{W}
\]

The right endpoint is excluded. Every canonical block has \(a_B\ge1\), so
\(0<a_B<b_B\) and \(w_B>0\).

T90's exact core domain is

\[
  D_{m,B}:=
  \left\{(r,n)\in\mathbb N^2:
    0<r,\ m\le r,\ a_B\le n+r,\ n+r<b_B
  \right\}.
  \tag{D}
\]

Write

\[
  K_B:=|D_{m,B}|,
  \qquad
  d_{r,n}:=10^n(10^r-1).
  \tag{F}
\]

For each \(p=(r,n)\in D_{m,B}\), the two ordered orientations are retained:

\[
  \mathrm{false}\longmapsto-d_{r,n},
  \qquad
  \mathrm{true}\longmapsto+d_{r,n}.
  \tag{S}
\]

The frequency multiplier is inclusively quantified:

\[
  h\in\{1,2,\ldots,H\}.
  \tag{I}
\]

The primitive frequencies in (F) are positive and injective on (D). For
positivity, \(r\ge m\ge1\) gives \(10^r-1>0\). For injectivity, the largest
power of ten dividing \(10^n(10^r-1)\) is exactly \(10^n\), because
\(10\nmid10^r-1\). Equality of two primitive frequencies therefore first
gives equality of the starts \(n\), and cancellation then gives equality of
the lags \(r\). This argument is included here, rather than importing an
additional theorem as a premise.

## 5. Exact variable-phase CORR sibling

For \(\alpha\in[0,1)\), define the real block sum

\[
  S_{B,h}(\alpha):=
  \sum_{(r,n)\in D_{m,B}}
    \cos\!\left(2\pi\alpha h\,10^n(10^r-1)\right).
  \tag{5.1}
\]

By (S), the two signed orientations of one core contribute

\[
  e^{-2\pi i\alpha h d_{r,n}}+e^{2\pi i\alpha h d_{r,n}}
  =2\cos(2\pi\alpha h d_{r,n}).
  \tag{5.2}
\]

Consequently the exact variable-phase width-weighted square function is

\[
  \mathcal W_{m,N}(\alpha)
  :=4\sum_{B\in\mathcal B_N}\frac1{w_B}
      \sum_{h=1}^{H}S_{B,h}(\alpha)^2.
  \tag{5.3}
\]

The factor four in (5.3) retains all four ordered choices of the two signs
after the block vector is squared. T87/T90's exact diagonal is

\[
  \mathcal D_{m,N}
  :=2H\sum_{B\in\mathcal B_N}\frac{K_B}{w_B}.
  \tag{5.4}
\]

Although T90 writes this as `recordDiagonal Q0 m N`, T87 proves that it is
independent of \(Q_0\) in the present \((8,1)\) range.

Define the centered finite observable

\[
\begin{aligned}
  X_{m,N}(\alpha)
  &:=\mathcal W_{m,N}(\alpha)-\mathcal D_{m,N}\\
  &=4\sum_{B\in\mathcal B_N}\frac1{w_B}
      \sum_{h=1}^{H}
       \left(S_{B,h}(\alpha)^2-\frac{K_B}{2}\right).
\end{aligned}
  \tag{5.5}
\]

The exact \(s=1/2\) critical normalization is

\[
  Z_{m,N}:=
  H\left(N+\frac{N^2}{\sqrt H}\right).
  \tag{5.6}
\]

The variable-phase sibling of T90's `CORR_pi` is the following proposition:

\[
\boxed{
\begin{aligned}
  \mathrm{CORR}_{\mathrm{var}}(\alpha):\quad
  \forall Q_0,m,N\in\mathbb N,
  &\ 1\le m\ \longrightarrow\ 1\le N\\
  &\longrightarrow H\le N^2
   \longrightarrow N^2\le2H\\
  &\longrightarrow X_{m,N}(\alpha)\le Z_{m,N},
  \qquad H=10^m.
\end{aligned}}
  \tag{CORR-var}
\]

This keeps \(Q_0\) in exactly T90's position. The conclusion happens not to
depend on it after the all-scale exclusion audit.

For a term-by-term comparison with T90, put

\[
  \Delta_{m,N}:=
  H\sum_{B\in\mathcal B_N}
    \frac{(2K_B)(2K_B-1)}{w_B}
  =4H\sum_{B\in\mathcal B_N}
    \frac{K_B^2-K_B/2}{w_B}
  \tag{5.7}
\]

and

\[
  A_{m,N}(\alpha):=
  4\sum_{B\in\mathcal B_N}\frac1{w_B}
    \sum_{h=1}^{H}\left(K_B^2-S_{B,h}(\alpha)^2\right).
  \tag{5.8}
\]

Direct subtraction gives the exact T90 alignment identity

\[
  X_{m,N}(\alpha)=\Delta_{m,N}-A_{m,N}(\alpha).
  \tag{5.9}
\]

Thus (CORR-var) is literally equivalent to

\[
  \Delta_{m,N}-Z_{m,N}\le A_{m,N}(\alpha),
  \tag{5.10}
\]

with every coefficient in T90 unchanged.

## 6. Exact finite Fourier expansion and moments

Fix any total order on each finite set \(D_{m,B}\). For
\(p=(r,n)\), abbreviate \(d_p=d_{r,n}\). The elementary identities

\[
  \cos^2x=\frac12+\frac12\cos(2x),
  \qquad
  2\cos x\cos y=\cos(x-y)+\cos(x+y)
\]

give, exactly,

\[
\begin{aligned}
 S_{B,h}(\alpha)^2-\frac{K_B}{2}
 ={}&\frac12\sum_{p\in D_{m,B}}
      \cos(2\pi\alpha\,2h d_p)\\
 &+\sum_{p<q}\cos(2\pi\alpha\,h|d_p-d_q|)\\
 &+\sum_{p<q}\cos(2\pi\alpha\,h(d_p+d_q)).
\end{aligned}
  \tag{6.1}
\]

Every frequency in (6.1) is a positive integer. Positivity in the difference
line uses injectivity of \(p\mapsto d_p\).

### 6.1 Weighted frequency events

Create one event for every occurrence of a term on the right of (6.1),
including its block occurrence and its multiplier \(h\). Give it frequency
\(\nu(e)\) and weight \(\gamma(e)\) as follows:

| event | frequency \(\nu(e)\) | weight \(\gamma(e)\) |
|---|---:|---:|
| \((B,h,p,\mathrm{double})\) | \(2h d_p\) | \(1/(2w_B)\) |
| \((B,h,p,q,\mathrm{difference})\), \(p<q\) | \(h|d_p-d_q|\) | \(1/w_B\) |
| \((B,h,p,q,\mathrm{sum})\), \(p<q\) | \(h(d_p+d_q)\) | \(1/w_B\) |

Derived frequencies need not be distinct. Therefore define grouped,
nonnegative coefficients

\[
  a_k(m,N):=\sum_{e:\,\nu(e)=k}\gamma(e),
  \qquad k\ge1.
  \tag{6.2}
\]

Only finitely many are nonzero. Equations (5.5) and (6.1) give the exact
grouped expansion

\[
\boxed{
  X_{m,N}(\alpha)=
  4\sum_{k\ge1}a_k(m,N)\cos(2\pi k\alpha).
}
  \tag{6.3}
\]

The total coefficient mass is

\[
\begin{aligned}
  \mathcal A_{m,N}
  :=\sum_{k\ge1}a_k(m,N)
  &=H\sum_{B\in\mathcal B_N}
      \frac{K_B/2+2\binom{K_B}{2}}{w_B}\\
  &=H\sum_{B\in\mathcal B_N}
      \frac{K_B^2-K_B/2}{w_B}
   =\frac{\Delta_{m,N}}4.
\end{aligned}
  \tag{6.4}
\]

### 6.2 Mean and second moment

For every nonzero integer \(u\), direct integration gives

\[
  \int_0^1e^{2\pi i u\alpha}\,d\alpha
  =\left[\frac{e^{2\pi i u\alpha}}{2\pi i u}\right]_0^1=0.
  \tag{6.5}
\]

Taking real parts yields

\[
  \int_0^1\cos(2\pi k\alpha)\,d\alpha=0
  \quad(k\ge1),
  \tag{6.6}
\]

and product-to-sum yields

\[
  \int_0^1\cos(2\pi k\alpha)\cos(2\pi\ell\alpha)\,d\alpha
  =\begin{cases}
    1/2,&k=\ell,\\
    0,&k\ne\ell.
  \end{cases}
  \tag{6.7}
\]

It follows from (6.3) that

\[
\boxed{\int_0^1X_{m,N}(\alpha)\,d\alpha=0.}
  \tag{6.8}
\]

Equivalently, the finite variable-phase square function has exact mean equal
to T87's record diagonal:

\[
  \int_0^1\mathcal W_{m,N}(\alpha)\,d\alpha
  =\mathcal D_{m,N}.
  \tag{6.9}
\]

Define the exact weighted pair-resonance count

\[
\begin{aligned}
  R_2(m,N)
  &:=\sum_{k\ge1}a_k(m,N)^2\\
  &=\sum_{e,e'}\gamma(e)\gamma(e')
       \mathbf 1_{\nu(e)=\nu(e')}.
\end{aligned}
  \tag{6.10}
\]

Then (6.3) and (6.7) give the exact finite second moment

\[
\boxed{
  \int_0^1X_{m,N}(\alpha)^2\,d\alpha=8R_2(m,N).
}
  \tag{6.11}
\]

Because every \(a_k\ge0\),

\[
  R_2(m,N)\le\mathcal A_{m,N}^2,
  \qquad
  \int_0^1X_{m,N}^2\le\frac12\Delta_{m,N}^2.
  \tag{6.12}
\]

The first inequality in (6.12) is deliberately crude; it is not summable at
the desired scale. The grouped resonance count (6.10), rather than a false
claim that all raw terms are orthogonal, is the narrower arithmetic object.

### 6.3 Exact fourth moment and an explicit bound

Define

\[
\begin{aligned}
  R_4(m,N):={}&
  \sum_{k_1,k_2,k_3,k_4\ge1}
  a_{k_1}a_{k_2}a_{k_3}a_{k_4}\\
  &\quad\cdot
  \#\left\{(\varepsilon_1,\ldots,\varepsilon_4)\in\{-1,1\}^4:
    \sum_{j=1}^4\varepsilon_jk_j=0
  \right\}.
\end{aligned}
  \tag{6.13}
\]

Expanding every cosine as
\((e^{2\pi ik\alpha}+e^{-2\pi ik\alpha})/2\) and using (6.5) gives

\[
\boxed{
  \int_0^1X_{m,N}(\alpha)^4\,d\alpha=16R_4(m,N).
}
  \tag{6.14}
\]

For completeness, extend \(a\) to \(c:\mathbb Z\to\mathbb R_{\ge0}\) by
\(c_0=0\) and \(c_j=a_{|j|}\) for \(j\ne0\). Then

\[
  R_4=\sum_{s\in\mathbb Z}(c*c)(s)^2.
\]

Finite discrete Young convolution gives

\[
\begin{aligned}
  R_4
  &\le\|c\|_1^2\|c\|_2^2\\
  &=(2\mathcal A_{m,N})^2(2R_2(m,N))
   =8\mathcal A_{m,N}^2R_2(m,N).
\end{aligned}
\]

Hence the explicit fourth-moment bounds are

\[
\boxed{
\begin{aligned}
  \int_0^1X_{m,N}^4
  &\le128\mathcal A_{m,N}^2R_2(m,N)\\
  &\le128\mathcal A_{m,N}^4
   =\frac12\Delta_{m,N}^4.
\end{aligned}}
  \tag{6.15}
\]

## 7. Maximal-tail reduction with constants

For each positive \(m\), define the exact finite critical set

\[
  \mathcal C_m:=
  \{N\in\mathbb N:1\le N,\ H\le N^2\le2H\},
  \qquad H=10^m,
  \tag{7.1}
\]

and its bad event

\[
  \mathcal E_m:=
  \{\alpha\in[0,1):
    \exists N\in\mathcal C_m,\ X_{m,N}(\alpha)>Z_{m,N}\}.
  \tag{7.2}
\]

Since \(\int X_{m,N}=0\), Chebyshev's inequality and (6.11) imply

\[
  \lambda\{\alpha:X_{m,N}(\alpha)>Z_{m,N}\}
  \le\frac{8R_2(m,N)}{Z_{m,N}^2}.
  \tag{7.3}
\]

The lower critical inequality \(H\le N^2\) gives \(\sqrt H\le N\), and
therefore

\[
  Z_{m,N}
  =H\left(N+\frac{N^2}{\sqrt H}\right)
  \ge2HN.
  \tag{7.4}
\]

Taking the finite union over every admissible \(N\), including both endpoint
cases, gives the explicit maximal-tail inequality

\[
\boxed{
  \lambda(\mathcal E_m)
  \le\frac{2}{H^2}
      \sum_{N\in\mathcal C_m}\frac{R_2(m,N)}{N^2},
  \qquad H=10^m.
}
  \tag{MT}
\]

No independence among the events is assumed.

The following is one explicit strictly narrower terminal input.

\[
\boxed{
\begin{aligned}
(\mathrm{RC}_{1/4}):\quad
\exists C\ge0\ \forall m\ge1,\qquad
\sum_{N\in\mathcal C_m}\frac{R_2(m,N)}{N^2}
\le C H^{7/4},\qquad H=10^m.
\end{aligned}}
  \tag{RC}
\]

Claim label for (RC): `conjecture`.

It is a strictly narrower terminal input in variables and mathematical
structure: (RC) is a finite, phase-free, weighted count of equal positive
integers among the three explicit frequency families in Section 6.1. It
contains no Fourier value at any fixed alpha, no maximal phase quantifier, no
collision count, and no reference to `pi`. This does not mean that (RC) is a
logically weaker reformulation of the all-scale (CORR-var); it is a sufficient
condition only for the eventual tail statement derived below.

Combining (MT) and (RC) gives, with no hidden constant,

\[
  \lambda(\mathcal E_m)\le2C H^{-1/4}=2C\,10^{-m/4}.
  \tag{7.5}
\]

Consequently, for every positive integer \(M\),

\[
\boxed{
  \lambda\!\left(\bigcup_{m\ge M}\mathcal E_m\right)
  \le
  \frac{2C\,10^{-M/4}}{1-10^{-1/4}}.
}
  \tag{7.6}
\]

The geometric series converges, so the elementary first Borel-Cantelli
argument gives the conditional eventual statement

\[
  \lambda\text{-a.e. }\alpha\in[0,1),\quad
  \exists m_0(\alpha)\ \forall m\ge m_0(\alpha)\
  \forall N\in\mathcal C_m,\quad
  X_{m,N}(\alpha)\le Z_{m,N}.
  \tag{7.7}
\]

Statement (7.7) is conditional on the conjecture (RC), and it is only an
eventual tail statement. It cannot repair a failure at a fixed finite scale.

## 8. Complete verdict on the almost-everywhere all-scale assertion

The full-measure assertion for (CORR-var) is false. This can be checked at
one retained positive critical-band pair, by exact finite calculation and
without a computational experiment.

Take

\[
  m=1,\qquad H=10,\qquad N=4.
\]

The inclusive critical-band endpoints give

\[
  10=H\le16=N^2\le20=2H.
\]

Since \(N-1=3=2^1+2^0\), the exact decreasing-level canonical partition of
\([1,4)\) is

\[
  B_1=[1,3),\qquad B_2=[3,4).
\]

Its literal widths are

\[
  w_{B_1}=\sqrt{3^2-1^2}=\sqrt8,
  \qquad
  w_{B_2}=\sqrt{4^2-3^2}=\sqrt7.
\]

Using the weak-left/strict-right endpoint convention in (D), the exact core
domains are

\[
\begin{aligned}
  D_{1,B_1}&=\{(1,0),(1,1),(2,0)\},\\
  D_{1,B_2}&=\{(1,2),(2,1),(3,0)\}.
\end{aligned}
\]

Thus \(K_{B_1}=K_{B_2}=3\). At \(\alpha=0\), all frequencies
\(h=1,\ldots,10\) are retained and every cosine in (5.1) equals one. Hence

\[
\begin{aligned}
  X_{1,4}(0)
  &=4\cdot10\left(3^2-\frac32\right)
       \left(\frac1{\sqrt8}+\frac1{\sqrt7}\right)\\
  &=300\left(\frac1{\sqrt8}+\frac1{\sqrt7}\right).
\end{aligned}
  \tag{8.1}
\]

Because \(\sqrt8<3\) and \(\sqrt7<3\),

\[
  X_{1,4}(0)>300\left(\frac13+\frac13\right)=200.
  \tag{8.2}
\]

On the other hand, \(\sqrt{10}>3\), so the exact normalization obeys

\[
\begin{aligned}
  Z_{1,4}
  &=10\left(4+\frac{16}{\sqrt{10}}\right)\\
  &<10\left(4+\frac{16}{3}\right)
   =\frac{280}{3}<200.
\end{aligned}
  \tag{8.3}
\]

Therefore

\[
  X_{1,4}(0)>Z_{1,4}.
  \tag{8.4}
\]

The function \(X_{1,4}\) is a finite sum of continuous cosine functions.
The strict inequality (8.4) therefore persists on some interval
\([0,\varepsilon)\) with \(\varepsilon>0\). This interval lies in the
failure set of (CORR-var), independently of \(Q_0\). The full failure set is
measurable: it is the countable union over positive integer triples
\((Q_0,m,N)\) satisfying (CB) of strict superlevel sets of finite continuous
trigonometric polynomials, intersected with \([0,1)\). Consequently

\[
\boxed{
  \lambda\{\alpha\in[0,1):
    \neg\mathrm{CORR}_{\mathrm{var}}(\alpha)\}>0,
}
  \tag{8.5}
\]

and hence

\[
\boxed{
  \lambda\{\alpha\in[0,1):
    \mathrm{CORR}_{\mathrm{var}}(\alpha)\}<1.
}
  \tag{8.6}
\]

This is the complete yes/no verdict on the assertion that the exact
coefficient-one, all-positive-scale CORR sibling holds almost everywhere: it
does not. Equation (8.5) does not claim that failure has measure one.

## 9. Resonance warning and inspectable example

Primitive frequency injectivity does not make the derived events in Section
6 orthogonal. Already in \(D_{1,B_1}\),

\[
  d_{1,0}=9,\qquad d_{1,1}=90,\qquad d_{2,0}=99.
\]

The derived frequency \(90\) occurs both as

\[
  |99-9|=90
\]

and as the doubled term

\[
  2\cdot5\cdot9=90
\]

when \(h=5\) for the primitive frequency \(9\). Thus the off-diagonal terms
in \(R_2\) are real and cannot be discarded. This is exactly why the grouped
coefficients \(a_k\) and the terminal resonance count (RC) are necessary.

## 10. Endpoint, sign, weight, constant, and conclusion checklist

| feature | retained form |
|---|---|
| phase probability space | Lebesgue measure on \([0,1)\), total mass one |
| positive scales | \(1\le m\), \(1\le N\) |
| critical band | \(10^m\le N^2\le2\cdot10^m\), both endpoints inclusive |
| canonical blocks | decreasing binary partition of \([1,N)\) |
| block endpoint test | \(a_B\le n+r<b_B\) |
| lag test | \(0<r\) and \(m\le r\) |
| arithmetic exclusions | literal \((\mu,c)=(8,1)\); none survive; \(Q_0\) retained |
| orientations/signs | both Boolean orientations, frequencies \(-d_{r,n}\) and \(+d_{r,n}\) |
| Fourier frequencies | every integer \(1\le h\le10^m\), upper endpoint included |
| width | \(w_B=\sqrt{b_B^2-a_B^2}\), no replacement or asymptotic surrogate |
| square factor | \(4\), retaining all four ordered sign products |
| diagonal | \(2\cdot10^m\sum_B K_B/w_B\) |
| normalization | \(10^m(N+N^2/\sqrt{10^m})\), exactly \(s=1/2\) |
| CORR coefficient | literal one; no alpha-dependent or scale-dependent constant |
| maximal-tail constant | literal \(2/H^2\) in (MT) |
| terminal exponent | literal \(H^{7/4}\), yielding \(2C10^{-m/4}\) |
| fixed-pi conclusion | none |
| C1, C2, C3 conclusion | none |
| canonical collision conclusion | none; this is sibling A12 only |

## 11. Outcome

1. `proof sketch`: the exact all-scale variable-phase sibling
   (CORR-var) is not an almost-everywhere property, because its failure set
   contains a nonempty interval at the retained critical pair \((m,N)=(1,4)\).
2. `proof sketch`: its centered finite observable has exact mean zero, exact
   second moment \(8R_2\), and exact fourth moment \(16R_4\).
3. `proof sketch`: the maximal bad-set measure satisfies the explicit bound
   (MT).
4. `conjecture`: the strictly narrower phase-free resonance inequality (RC)
   would imply the explicit eventual-tail estimate (7.6), but cannot restore
   the already-refuted all-scale full-measure assertion.
5. No computational experiment was used as proof or evidence in this note;
   Section 8 is an exact symbolic calculation on finite sets.
