# T95: Eventual constant-relaxed variable-phase centered critical band

Claim label: `proof sketch`.

This is a self-contained rigorous prose note. Its only established inputs are
the kernel-checked T87 and T90 interfaces listed below. The T92 note is used
only as motivation for asking an eventual, constant-relaxed question; no
claim or calculation from T92 is a premise here.

## 1. Provenance, source, and scope

- Canonical local statement: `CANONICAL_STATEMENT.txt`.
- Canonical SHA-256:
  `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`.
- Original external source URL: none. The canonical statement says that the
  system formulated the question on 2026-07-23.
- Sibling status: this note concerns only T29's residual sparse-Fourier
  sibling A12. It is not a statement about the canonical collision count.
- Literature: no external result is used. All Fourier integrals, valuation
  classifications, and finite estimates used below are proved in the note.
  No novelty claim is made.

The canonical question asks for an all-scale fixed-pi collision estimate.
The present question is different: only the value inserted into the Fourier
phases is replaced by a Lebesgue-random variable.

## 2. Normalized statement and ambiguities

Lebesgue measure restricted to the half-open interval `[0,1)` is denoted by
`lambda`; thus `lambda([0,1))=1`. Put

\[
  H=10^m.
\]

The phrase "replace pi only in the Fourier phases" means that T90's

\[
  \cos(2\pi^2 h d)
\]

is replaced by

\[
  \cos(2\pi\alpha h d),
\]

not by `cos(2 alpha^2 h d)` and not by `cos(2 pi^2 alpha h d)`.

The exact eventual constant-relaxed assertion under investigation is

\[
\boxed{
\begin{aligned}
  \lambda\text{-a.e. }\alpha\in[0,1),\quad
  &\exists B_\alpha\in[1,\infty)\ \exists m_0(\alpha)\in\mathbb N\quad
  \forall m\in\mathbb N,\ m\ge m_0(\alpha),\\
  &\forall N\in\mathbb N,\quad
    1\le m\ \wedge\ 1\le N\ \wedge\
    10^m\le N^2\le2\cdot10^m\\
  &\Longrightarrow
    \forall Q_0\in\mathbb N,\quad
    X_{Q_0,m,N}(\alpha)\le B_\alpha Z_{m,N}.
\end{aligned}}
\tag{EV}
\]

The order is important: `B_alpha` and `m0(alpha)` occur before every later
`m`, critical-band `N`, and arbitrary `Q0`. The constant cannot depend on
`m`, `N`, or `Q0`. The estimate is one-sided, just as T90's centered
condition is; replacing it by an absolute-value estimate would be stronger.
Both critical-band endpoints are included. Finite exceptional scales may be
absorbed by `m0(alpha)`, so a fixed-scale failure cannot decide (EV).

The formula below is independent of `Q0`, but `Q0` remains quantified in
exactly the required position. This independence is a consequence of the
all-scale arithmetic-exclusion audit, not a deletion of the quantifier.

## 3. Established T87/T90 interfaces

The following kernel-checked facts are used.

From T87:

1. `not_arithmeticExcluded_eight_one` removes every T22 arithmetic exclusion
   at `(mu,c)=(8,1)`, for every positive `m`, admissible lag, and arbitrary
   `Q0`.
2. `blockRecordDomain_both_orientations_eight_one` retains exactly the two
   Boolean orientations, with signed frequencies `-d` and `+d`, weak left
   endpoint, and strict right endpoint.
3. `inclusiveFrequencies_card_exact` gives exactly the inclusive frequencies
   `h=1,...,10^m`.
4. `recordDiagonal_exact_formula_literal` and
   `recordDiagonal_normalized_critical_bounds_literal` expose every canonical
   block, literal square-root width, exact diagonal, critical band, and
   normalization.
5. `blockRecordMass_le_width` bounds each exact record cardinality divided by
   its literal width by that width.

From T90:

1. `mem_blockCoreDomain_literal` gives the exact lower-dimensional core
   domain.
2. `blockRecordDomain_eight_one_eq_orientations` and
   `blockCoreDomain_orientation_exclusion_audit` identify the record domain
   with two signed copies of the core domain, with no hidden exclusion.
3. `two_orientations_phase_eq_cosine` fixes the Fourier-kernel sign
   convention. Its elementary exponential calculation gives the stated
   variable-phase replacement.
4. `blockSquaredEnergy_eight_one_pi_eq_coreSum`,
   `widthWeightedSquareFunction_eight_one_pi_eq_coreSum`, and
   `recordDiagonal_eq_coreCard` fix the factor four, all blocks, all
   frequencies, the diagonal, and every width.
5. `criticalNormalization_eq_T29_half` identifies the displayed target with
   T29's exact `s=1/2` normalization.

No assertion of T90's unproved `CORR_pi` is used.

## 4. Literal finite domains and signs

Fix positive `m,N` in the critical band

\[
  H=10^m\le N^2\le2H.
\tag{CB}
\]

Let `B_N` be T29's ordered list `translatedCanonicalBlocks N`. A block
`B` has natural-number endpoints

\[
  [a_B,b_B)=[B.\mathrm{start},B.\mathrm{finish})
\]

and literal width

\[
  w_B=\sqrt{b_B^2-a_B^2}>0.
\tag{4.1}
\]

The blocks form the decreasing-binary canonical partition of `[1,N)`. In
particular, adjacent endpoints telescope, so

\[
  \sum_{B\in\mathcal B_N}w_B^2
  =\sum_B(b_B^2-a_B^2)=N^2-1.
\tag{4.2}
\]

For completeness, (4.2) follows directly by induction on the recursive
definition `dyadicPartitionFrom`: its first block starts at the current
endpoint plus one, has length `2^j`, and the recursive tail starts at its
finish. The bit-index identity says that the final finish is `N`.

The exact T90 core domain is

\[
  D_{m,B}=\{(r,n)\in\mathbb N^2:
    0<r,\ m\le r,\ a_B\le n+r<b_B\}.
\tag{4.3}
\]

Write

\[
  K_B=|D_{m,B}|,\qquad R_r=10^r-1,\qquad
  d_{r,n}=10^nR_r.
\tag{4.4}
\]

Since `r>=m>=1`, every `d_(r,n)` is positive. It has exactly `n` trailing
decimal zeroes because `R_r` is odd and is not divisible by five. Therefore
`d_(r,n)=d_(s,l)` first forces `n=l`, and then forces `r=s`. Thus the
primitive frequencies are injective.

For every core `p=(r,n)`, the two orientations and signs are literally

\[
  \mathrm{false}\mapsto-d_{r,n},\qquad
  \mathrm{true}\mapsto+d_{r,n}.
\tag{4.5}
\]

The multiplier range is exactly

\[
  1\le h\le H,
\tag{4.6}
\]

including `h=H` and excluding frequency zero.

## 5. Exact variable-phase observable

For `alpha in [0,1)`, define

\[
  S_{B,h}(\alpha)=
  \sum_{(r,n)\in D_{m,B}}
  \cos(2\pi\alpha h d_{r,n}).
\tag{5.1}
\]

The two signs in (4.5) contribute

\[
  e^{-2\pi i\alpha h d}+e^{2\pi i\alpha h d}
  =2\cos(2\pi\alpha h d).
\tag{5.2}
\]

After squaring, all four ordered sign choices are retained. Hence the exact
variable-phase square function and T87 diagonal are

\[
  \mathcal W_{m,N}(\alpha)
  =4\sum_{B\in\mathcal B_N}\frac1{w_B}
    \sum_{h=1}^{H}S_{B,h}(\alpha)^2,
\tag{5.3}
\]

\[
  \mathcal D_{Q_0,m,N}
  =2H\sum_{B\in\mathcal B_N}\frac{K_B}{w_B}.
\tag{5.4}
\]

Formula (5.4) is independent of `Q0` after T87's exclusion audit, while the
subscript records the preserved quantifier. Define

\[
\begin{aligned}
  X_{Q_0,m,N}(\alpha)
  &=\mathcal W_{m,N}(\alpha)-\mathcal D_{Q_0,m,N}\\
  &=4\sum_{B\in\mathcal B_N}\frac1{w_B}
    \sum_{h=1}^{H}\left(S_{B,h}(\alpha)^2-\frac{K_B}{2}\right),
\end{aligned}
\tag{5.5}
\]

and retain T90's exact `s=1/2` normalization

\[
  Z_{m,N}=H\left(N+\frac{N^2}{\sqrt H}\right).
\tag{5.6}
\]

## 6. Exact event expansion

Fix an arbitrary total order on each finite `D_(m,B)`. For every occurrence
in a block, create the following base events. Occurrences are retained as a
multiset: equal numerical frequencies arising from different records are not
silently identified.

| event `x` | base frequency `beta_x` | weight `gamma_x` |
|---|---:|---:|
| double `(B,p,D)` | `2 d_p` | `1/(2 w_B)` |
| difference `(B,p,q,-)`, `p<q` | `|d_p-d_q|` | `1/w_B` |
| sum `(B,p,q,+)`, `p<q` | `d_p+d_q` | `1/w_B` |

All base frequencies are positive integers. The difference is nonzero by
primitive injectivity. The identities

\[
  \cos^2x=\frac12+\frac12\cos(2x),\qquad
  2\cos x\cos y=\cos(x-y)+\cos(x+y)
\]

give the exact expansion

\[
  X_{Q_0,m,N}(\alpha)
  =4\sum_{x\in E_0(m,N)}\gamma_x
    \sum_{h=1}^{H}\cos(2\pi\alpha h\beta_x).
\tag{6.1}
\]

Define the grouped nonnegative coefficient

\[
  a_k=\sum_{\substack{x\in E_0,\ 1\le h\le H\\h\beta_x=k}}\gamma_x,
  \qquad k\ge1.
\tag{6.2}
\]

Then, with only finitely many nonzero terms,

\[
  X_{Q_0,m,N}(\alpha)=4\sum_{k\ge1}a_k\cos(2\pi k\alpha).
\tag{6.3}
\]

The total coefficient mass is

\[
\begin{aligned}
  A_{m,N}:=\sum_{k\ge1}a_k
  &=H\sum_{B\in\mathcal B_N}
    \frac{K_B/2+2\binom{K_B}{2}}{w_B}\\
  &=H\sum_B\frac{K_B^2-K_B/2}{w_B}.
\end{aligned}
\tag{6.4}
\]

Thus T90's triangle majorant is exactly

\[
  \Delta_{m,N}=4A_{m,N}.
\tag{6.5}
\]

## 7. Replayable equal-frequency classification

### 7.1 Decimal valuation table

For a positive integer `u`, let `v_2(u)` and `v_5(u)` be its ordinary prime
valuations and define its decimal valuation by

\[
  v_{10}(u)=\min(v_2(u),v_5(u)).
\tag{7.1}
\]

This is the number of trailing decimal zeroes. It is not generally additive
under multiplication, which is why both prime valuations are retained.

Let `p=(r,n)` and `q=(s,l)` be distinct cores. The exact valuations of every
base event are as follows.

1. Double:

\[
  \beta=2d_{r,n}:
  \quad (v_2(\beta),v_5(\beta),v_{10}(\beta))=(n+1,n,n).
\tag{7.2}
\]

2. Unequal starts `n<l` (the case `l<n` is symmetric):

\[
  d_{r,n}\mathbin\pm d_{s,l}
  =10^n(R_r\mathbin\pm10^{l-n}R_s).
\tag{7.3}
\]

For the absolute difference, choose the sign after comparing the two positive
terms. In either the sum or difference, the parenthesis is congruent to `9`
or `1` modulo `10`; it is odd and not divisible by five. Therefore

\[
  (v_2(\beta),v_5(\beta),v_{10}(\beta))=(n,n,n).
\tag{7.4}
\]

3. Equal starts, difference. Here `r!=s`, and

\[
\begin{aligned}
  |d_{r,n}-d_{s,n}|
  &=10^n|10^r-10^s|\\
  &=10^{n+\min(r,s)}(10^{|r-s|}-1).
\end{aligned}
\tag{7.5}
\]

Hence

\[
  (v_2(\beta),v_5(\beta),v_{10}(\beta))
  =(n+\min(r,s),n+\min(r,s),n+\min(r,s)).
\tag{7.6}
\]

4. Equal starts, sum. Put `a=min(r,s)` and `b=max(r,s)`. Then

\[
  d_{r,n}+d_{s,n}=10^n(10^r+10^s-2).
\tag{7.7}
\]

The parenthesis is `8 mod 10`, so its 5-adic valuation is zero. Its exact
2-adic valuation `c(r,s)` is

\[
  c(r,s)=
  \begin{cases}
    1,&a\ge2,\\
    2,&a=1,\ b=2,\\
    4,&a=1,\ b=3,\\
    3,&a=1,\ b\ge4.
  \end{cases}
\tag{7.8}
\]

Indeed, for `a>=2` the parenthesis is `2 mod 4`; for `a=1` it is
`8+10^b`, giving the other three cases modulo the next power of two. Thus

\[
  (v_2(\beta),v_5(\beta),v_{10}(\beta))
  =(n+c(r,s),n,n).
\tag{7.9}
\]

For a derived frequency `h beta`, the exact prime valuations are

\[
  v_2(h\beta)=v_2(h)+v_2(\beta),\qquad
  v_5(h\beta)=v_5(h)+v_5(\beta),
\tag{7.10}
\]

and its decimal valuation is their minimum. This explicitly includes the
extra trailing zero in examples such as `5*(2*9)=90`; replacing (7.10) by a
false additive rule for `v_10` would miss that resonance.

### 7.2 Complete equality criterion

The valuation table is a fast necessary classifier, but valuations alone do
not determine a positive integer. For a complete classification, uniquely
write

\[
  \beta=2^x5^y u,\qquad \gcd(u,10)=1,
\tag{7.11}
\]

where `(x,y)` is supplied by (7.2)-(7.9). Two derived frequencies can be
equal only if their 2-adic valuations, 5-adic valuations, and coprime-to-ten
parts agree after multiplication by `h` and `h'`. Equivalently, for any two
base-event occurrences `x,y`, let

\[
  g=\gcd(\beta_x,\beta_y),\qquad
  A=\beta_x/g,\qquad B=\beta_y/g.
\tag{7.12}
\]

Then `gcd(A,B)=1`, and the exact necessary-and-sufficient classification is

\[
  h\beta_x=h'\beta_y
  \quad\Longleftrightarrow\quad
  (h,h')=(Bt,At)
\tag{7.13}
\]

for one positive integer `t`. Consequently, the exact number of ordered
multiplier pairs in the inclusive square `[1,H]^2` is

\[
  L_H(\beta_x,\beta_y)
  =\left\lfloor
    \frac{H\gcd(\beta_x,\beta_y)}
         {\max(\beta_x,\beta_y)}
   \right\rfloor.
\tag{7.14}
\]

Equations (7.2)-(7.14) classify every equal derived frequency, including
cross-type and cross-block equalities. For example, an equal-start difference
in (7.5) is itself another primitive repunit frequency; it must not be
declared orthogonal to the double or sum families merely because its event
label differs.

## 8. Exact moments and an unconditional strict saving

For every nonzero integer `u`, direct integration gives

\[
  \int_0^1 e^{2\pi i u\alpha}\,d\alpha=0.
\tag{8.1}
\]

Therefore

\[
  \int_0^1\cos(2\pi k\alpha)\cos(2\pi l\alpha)\,d\alpha
  =\frac12\mathbf1_{k=l}\qquad(k,l\ge1).
\tag{8.2}
\]

It follows from (6.3) that

\[
  \int_0^1X_{Q_0,m,N}(\alpha)\,d\alpha=0,
\tag{8.3}
\]

and, defining

\[
  R_2(m,N)=\sum_{k\ge1}a_k^2,
\tag{8.4}
\]

the exact finite second moment is

\[
\boxed{
  \int_0^1X_{Q_0,m,N}(\alpha)^2\,d\alpha=8R_2(m,N).
}
\tag{8.5}
\]

There is an unconditional power saving over the direct majorant. For fixed
`k` and fixed base occurrence `x`, at most one multiplier `h` can satisfy
`h beta_x=k`. All weights are positive, so

\[
  a_k\le\sum_{x\in E_0}\gamma_x=\frac{A_{m,N}}H.
\tag{8.6}
\]

Using `sum a_k=A_(m,N)` gives

\[
  R_2(m,N)\le(\max_k a_k)\sum_k a_k
  \le\frac{A_{m,N}^2}{H}.
\tag{8.7}
\]

Since the direct pointwise triangle estimate from (6.1) is
`|X|<=4A=Delta`, (8.5)-(8.7) give the strict quantitative saving

\[
\boxed{
  \int_0^1X_{Q_0,m,N}^2
  \le\frac{8A_{m,N}^2}{H}
  =\frac{\Delta_{m,N}^2}{2H}.
}
\tag{8.8}
\]

Thus the second-moment bound saves the full factor `H=10^m` relative to the
ungrouped estimate `R_2<=A^2`, and the factor `2H` relative to squaring the
pointwise direct majorant. It is genuinely strict in (CB): T87's critical
lower bound gives `m<N`, so the endpoint `m` belongs to one canonical block
and the core `(r,n)=(m,0)` belongs to that block. Hence `A_(m,N)>0`, while
`H=10^m>=10`.

For scale, T87's `blockRecordMass_le_width` and T90's exact record cardinality
give

\[
  \frac{2K_B}{w_B}\le w_B,
  \qquad K_B\le\frac{w_B^2}{2}.
\tag{8.9}
\]

Consequently, using (4.2),

\[
\begin{aligned}
  A_{m,N}
  &\le H\sum_B\frac{K_B^2}{w_B}
   \le\frac H4\sum_Bw_B^3\\
  &\le\frac H4\left(\max_Bw_B\right)\sum_Bw_B^2
   \le\frac{HN(N^2-1)}4.
\end{aligned}
\tag{8.10}
\]

This bound confirms that (8.8), although a strict power saving, is not by
itself summable at the critical scale. The remaining issue is the covariance
among distinct base-event occurrences.

## 9. Exact diagonal and the single covariance obstruction

Regard `(x,h)` as a raw event. Its contribution to `R_2` is diagonal when the
two raw event indices are identical. For a block with `K=K_B`, the sum of
squared weights for one multiplier is exactly

\[
  K\left(\frac1{2w_B}\right)^2
  +2\binom K2\left(\frac1{w_B}\right)^2
  =\frac{K^2-3K/4}{w_B^2}.
\tag{9.1}
\]

Therefore the exact raw diagonal is

\[
  D_2(m,N)=H\sum_{B\in\mathcal B_N}
    \frac{K_B^2-3K_B/4}{w_B^2}.
\tag{9.2}
\]

By (8.9) and (4.2),

\[
\boxed{
  0\le D_2(m,N)\le\frac H4\sum_Bw_B^2
  =\frac{H(N^2-1)}4.
}
\tag{9.3}
\]

Define the ordered off-diagonal covariance by the single explicit finite sum

\[
\boxed{
\begin{aligned}
  \mathfrak C(m,N)
  &:=R_2(m,N)-D_2(m,N)\\
  &=\sum_{\substack{x,y\in E_0(m,N)\\x\ne y}}
    \gamma_x\gamma_y
    \left\lfloor
      \frac{H\gcd(\beta_x,\beta_y)}
           {\max(\beta_x,\beta_y)}
    \right\rfloor.
\end{aligned}}
\tag{9.4}
\]

This is an ordered sum. No extra factor two is missing. Formula (9.4) follows
from the complete collision classification (7.13)-(7.14). It is nonnegative,
phase-free, finite, and contains every doubled, difference, and sum event,
including cross-block and cross-type coincidences. It is the only unbounded
term left after (9.3).

## 10. Maximal tail and terminal covariance inequality

Let

\[
  \mathcal C_m=\{N\in\mathbb N:1\le N,\ H\le N^2\le2H\}.
\tag{10.1}
\]

The lower critical inequality gives `sqrt(H)<=N`, hence

\[
  Z_{m,N}=H\left(N+\frac{N^2}{\sqrt H}\right)\ge2HN.
\tag{10.2}
\]

Let

\[
  \mathcal E_m=
  \{\alpha\in[0,1):\exists N\in\mathcal C_m,
    \ X_{0,m,N}(\alpha)>Z_{m,N}\}.
\tag{10.3}
\]

The choice `Q0=0` only binds the notation: (5.4)-(5.5) show, using T87's
exclusion audit, that the same set results for every `Q0`. Chebyshev's
inequality, (8.5), (10.2), and a finite union bound give

\[
\begin{aligned}
  \lambda(\mathcal E_m)
  &\le\sum_{N\in\mathcal C_m}
    \frac{8R_2(m,N)}{Z_{m,N}^2}\\
  &\le\frac2{H^2}\sum_{N\in\mathcal C_m}
    \frac{D_2(m,N)+\mathfrak C(m,N)}{N^2}.
\end{aligned}
\tag{10.4}
\]

Every critical `N` is at most `sqrt(2H)<2sqrt(H)`, so
`|C_m|<=2sqrt(H)`. Equation (9.3) therefore gives the unconditional diagonal
tail

\[
  \frac2{H^2}\sum_{N\in\mathcal C_m}\frac{D_2(m,N)}{N^2}
  \le H^{-1/2}.
\tag{10.5}
\]

The entire remaining metric gap is the following one displayed covariance
inequality, with one scale-independent constant:

\[
\boxed{
  (\mathrm{COV}_{1/4})\qquad
  \exists C_0\ge0\ \forall m\ge1,\qquad
  \sum_{N\in\mathcal C_m}
    \frac{\mathfrak C(m,N)}{N^2}
  \le C_0 H^{7/4},\qquad H=10^m.
}
\tag{10.6}
\]

Claim label for (10.6): `conjecture`.

If (10.6) holds, then (10.4)-(10.5) give the explicit maximal-tail estimate

\[
\boxed{
  \lambda(\mathcal E_m)
  \le H^{-1/2}+2C_0H^{-1/4}
  =10^{-m/2}+2C_0\,10^{-m/4}.
}
\tag{10.7}
\]

In particular, for every positive `M`,

\[
\boxed{
\begin{aligned}
  \lambda\left(\bigcup_{m\ge M}\mathcal E_m\right)
  \le{}&\frac{10^{-M/2}}{1-10^{-1/2}}\\
  &+\frac{2C_0\,10^{-M/4}}{1-10^{-1/4}}.
\end{aligned}}
\tag{10.8}
\]

Both geometric series converge because the scale is exactly `H=10^m`, not
an arbitrary integer tending to infinity. The first Borel-Cantelli lemma then
proves, conditional only on (10.6),

\[
  \lambda\text{-a.e. }\alpha,\quad
  \exists m_0(\alpha)\ \forall m\ge m_0(\alpha)\
  \forall N\in\mathcal C_m\ \forall Q_0,\quad
  X_{Q_0,m,N}(\alpha)\le Z_{m,N}.
\tag{10.9}
\]

This is stronger than (EV), with the admissible choice `B_alpha=1`. No
independence of scales or bad events is used.

## 11. Verdict and audit checklist

The unconditional verdict is outcome three allowed by the agenda item:

1. The exact finite second moment is (8.5).
2. Equal derived frequencies are completely classified by the decimal and
   prime valuation table (7.2)-(7.10), the coprime-to-ten remainder, and the
   exact gcd parametrization (7.12)-(7.14).
3. The strict unconditional estimate (8.8) saves a full factor `10^m` over
   the grouped direct-majorant moment bound.
4. The raw diagonal already has the summable maximal tail (10.5).
5. The eventual constant-relaxed assertion (EV) is not claimed proved or
   refuted. The sole remaining input in this route is the explicit ordered
   covariance inequality (10.6); if it holds, (10.7)-(10.9) prove even the
   coefficient-one eventual assertion.

| feature | exact retained form |
|---|---|
| probability space | Lebesgue measure on `[0,1)`, total mass one |
| phase replacement | `cos(2 pi alpha h d)` only |
| positive scales | `1<=m`, `1<=N` |
| critical band | `10^m<=N^2<=2*10^m`, endpoints included |
| canonical blocks | every block in `translatedCanonicalBlocks N` |
| core endpoint | `a_B<=n+r<b_B` |
| lag | `0<r` and `m<=r` |
| arithmetic exclusion | `(mu,c)=(8,1)`; none survive; arbitrary `Q0` retained |
| orientations and signs | both Boolean orientations, `-d` and `+d` |
| multiplier frequency | every `h=1,...,10^m`, inclusive |
| width | `sqrt(b_B^2-a_B^2)` literally |
| square factor | `4`, retaining all ordered sign products |
| diagonal | `2*10^m*sum_B K_B/w_B` |
| normalization | `10^m*(N+N^2/sqrt(10^m))`, exactly `s=1/2` |
| eventual constants | `B_alpha,m0(alpha)` precede every later `m,N,Q0` |
| fixed pi | no conclusion |
| C1, C2, C3 | no conclusion |
| canonical collision count | no conclusion; this is sibling A12 only |
