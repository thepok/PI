# T96: Equal-start covariance for the eventual variable-phase critical band

Claim label: `proof sketch`.

## 1. Provenance and scope

- Canonical local statement: `CANONICAL_STATEMENT.txt`.
- Canonical SHA-256:
  `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`.
- Original external source URL: none. The canonical statement records that the
  system formulated the question on 2026-07-23.
- Established inputs: only the kernel-checked T87 and T90 interfaces listed in
  Section 3.
- Motivation only: the T95 note is an unverified sketch. No assertion from it
  is used as a premise below.

This note concerns the eventual variable-phase version of T29's residual
sparse-Fourier sibling A12. It is not the canonical fixed-pi collision
question. It proves a complete estimate for the equal-start covariance sector
and reduces all remaining covariance to one strictly narrower unequal-start
inequality. It does not prove that narrower inequality.

No conclusion is stated for pi, C1, C2, C3, or the canonical collision count.

## 2. Normalized statement and quantifier audit

Lebesgue measure on `[0,1)` is denoted by `lambda`, with total mass one. Put

\[
  H=10^m.
\tag{2.1}
\]

The variable-phase replacement is only

\[
  \cos(2\pi^2 h d)\quad\longmapsto\quad
  \cos(2\pi\alpha h d),\qquad \alpha\in[0,1).
\tag{2.2}
\]

In particular, it is not `cos(2 alpha^2 h d)` and not
`cos(2 pi^2 alpha h d)`.

The eventual sibling assertion motivating the covariance problem has the
literal quantifier order

\[
\begin{aligned}
  \lambda\text{-a.e. }\alpha\in[0,1),\quad
  &\exists B_\alpha\ge1\ \exists m_0(\alpha)\in\mathbb N\quad
  \forall m\ge m_0(\alpha),\\
  &\forall N\in\mathbb N,\quad
  1\le m,\ 1\le N,\ 10^m\le N^2\le2\cdot10^m\\
  &\Longrightarrow \forall Q_0\in\mathbb N,\quad
  X_{Q_0,m,N}(\alpha)\le B_\alpha Z_{m,N}.
\end{aligned}
\tag{EV}
\]

Here

\[
  Z_{m,N}=H\left(N+\frac{N^2}{\sqrt H}\right).
\tag{2.3}
\]

Thus `B_alpha` and `m0(alpha)` precede every later `m`, critical-band `N`,
and arbitrary `Q0`. The estimate is one-sided. Both critical-band endpoints
are included. The formula below becomes independent of `Q0` only after the
T87 exclusion audit; the quantifier is retained rather than deleted.

The phrase "equal start" has one possible ambiguity. In this note it refers
to the two primitive cores inside one pair event. Covariance has two event
indices, so the resulting covariance partition has four ordered sectors, not
two. Section 6 makes this exhaustive partition explicit.

## 3. Kernel-checked interfaces used

The following are established inputs.

From T87:

1. `not_arithmeticExcluded_eight_one` removes every arithmetic exclusion at
   `(mu,c)=(8,1)` for positive `m`, admissible lag, and arbitrary `Q0`.
2. `blockRecordDomain_both_orientations_eight_one` retains both Boolean
   orientations, with signed frequencies `-d` and `+d`, weak left endpoint,
   and strict right endpoint.
3. `inclusiveFrequencies_card_exact` retains exactly `h=1,...,10^m`, including
   `10^m` and excluding zero.
4. `blockRecordMass_le_width` bounds the exact record count divided by the
   literal width by that width.
5. `recordDiagonal_exact_formula_literal` and
   `recordDiagonal_normalized_critical_bounds_literal` fix the exact diagonal,
   canonical blocks, widths, critical band, and normalization.

From T90:

1. `mem_blockCoreDomain_literal` gives the exact core domain.
2. `blockRecordDomain_eight_one_eq_orientations` and
   `blockCoreDomain_orientation_exclusion_audit` identify the record domain
   with two signed copies of the core domain.
3. `two_orientations_phase_eq_cosine` fixes the sign convention.
4. `blockSquaredEnergy_eight_one_pi_eq_coreSum`,
   `widthWeightedSquareFunction_eight_one_pi_eq_coreSum`, and
   `recordDiagonal_eq_coreCard` fix the factor four and the diagonal after
   quotienting the two orientations.
5. `criticalNormalization_eq_T29_half` fixes (2.3) as T29's `s=1/2`
   normalization after multiplication by `H`.

T90's proposition `CORR_pi` is not assumed.

## 4. Literal finite domains, signs, and widths

Fix integers `m,N` satisfying

\[
  1\le m,\qquad 1\le N,\qquad H=10^m\le N^2\le2H.
\tag{4.1}
\]

Let `B_N` be T29's ordered list `translatedCanonicalBlocks N`. Write a block
as

\[
  B=[a_B,b_B),\qquad L_B=b_B-a_B,
\tag{4.2}
\]

and retain the literal width

\[
  w_B=\sqrt{b_B^2-a_B^2}
      =\sqrt{L_B(a_B+b_B)}>0.
\tag{4.3}
\]

The exact T90 core domain is

\[
  D_{m,B}=\{(r,n)\in\mathbb N^2:
    0<r,\ m\le r,\ a_B\le n+r<b_B\}.
\tag{4.4}
\]

Put

\[
  K_B=|D_{m,B}|,\qquad R_r=10^r-1,\qquad
  d_{r,n}=10^nR_r.
\tag{4.5}
\]

Every `d_(r,n)` is positive. Since `R_r` is odd and not divisible by five,
`d_(r,n)` has exactly `n` trailing decimal zeroes. Hence

\[
  d_{r,n}=d_{s,l}\quad\Longleftrightarrow\quad(r,n)=(s,l).
\tag{4.6}
\]

For every core, the two literal orientations are

\[
  \mathrm{false}\mapsto-d_{r,n},\qquad
  \mathrm{true}\mapsto+d_{r,n}.
\tag{4.7}
\]

The multiplier range is exactly

\[
  1\le h\le H=10^m.
\tag{4.8}
\]

No arithmetic exclusion survives, independently of `Q0`.

## 5. Exact event expansion and covariance

For `alpha in [0,1)`, define

\[
  S_{B,h}(\alpha)=
    \sum_{(r,n)\in D_{m,B}}
      \cos(2\pi\alpha h d_{r,n}).
\tag{5.1}
\]

The two signs in (4.7) contribute `2 cos(2 pi alpha h d)`. Therefore the
exact variable-phase observable and T87 diagonal are

\[
  \mathcal W_{m,N}(\alpha)
  =4\sum_{B\in\mathcal B_N}\frac1{w_B}
      \sum_{h=1}^H S_{B,h}(\alpha)^2,
\tag{5.2}
\]

\[
  \mathcal D_{Q_0,m,N}
  =2H\sum_{B\in\mathcal B_N}\frac{K_B}{w_B}.
\tag{5.3}
\]

Formula (5.3) is independent of `Q0` because of the T87 audit, but the
subscript records the required quantifier. Set

\[
\begin{aligned}
  X_{Q_0,m,N}(\alpha)
  &=\mathcal W_{m,N}(\alpha)-\mathcal D_{Q_0,m,N}\\
  &=4\sum_B\frac1{w_B}\sum_{h=1}^H
    \left(S_{B,h}(\alpha)^2-\frac{K_B}{2}\right).
\end{aligned}
\tag{5.4}
\]

Choose any total order on each finite `D_(m,B)`. The base-event set `E_0` is
a set of tagged occurrences, so events from different blocks or different
core pairs remain distinct even if their numerical frequencies agree. For
each block create:

| event occurrence `x` | base frequency `beta_x` | weight `gamma_x` |
|---|---:|---:|
| double `J(B,p)` | `2 d_p` | `1/(2w_B)` |
| difference `M(B,p,q)`, `p<q` | `|d_p-d_q|` | `1/w_B` |
| sum `P(B,p,q)`, `p<q` | `d_p+d_q` | `1/w_B` |

All base frequencies are positive by (4.6). The identities

\[
  \cos^2x-\frac12=\frac12\cos(2x),\qquad
  2\cos x\cos y=\cos(x-y)+\cos(x+y)
\tag{5.5}
\]

give the exact finite expansion

\[
  X_{Q_0,m,N}(\alpha)
  =4\sum_{x\in E_0}\gamma_x
    \sum_{h=1}^H\cos(2\pi\alpha h\beta_x).
\tag{5.6}
\]

For `k>=1`, group equal derived frequencies by

\[
  a_k=\sum_{\substack{x\in E_0,\ 1\le h\le H\\h\beta_x=k}}\gamma_x.
\tag{5.7}
\]

Only finitely many `a_k` are nonzero and

\[
  X_{Q_0,m,N}(\alpha)=4\sum_{k\ge1}a_k\cos(2\pi k\alpha).
\tag{5.8}
\]

For positive integers `u,v`, let

\[
  L_H(u,v)=|\{(h,h')\in[1,H]^2:hu=h'v\}|.
\tag{5.9}
\]

Writing `g=gcd(u,v)`, `u=gA`, and `v=gB`, with `gcd(A,B)=1`, all solutions
are `(h,h')=(Bt,At)`. Thus the exact inclusive multiplier count is

\[
  \boxed{L_H(u,v)=
  \left\lfloor\frac{H\gcd(u,v)}{\max(u,v)}\right\rfloor.}
\tag{5.10}
\]

Orthogonality on `[0,1)` gives

\[
  \int_0^1\cos(2\pi k\alpha)\cos(2\pi l\alpha)\,d\alpha
  =\frac12\mathbf1_{k=l}.
\tag{5.11}
\]

Consequently, with `R_2=sum_k a_k^2`, both the moment and its raw-event
expansion are exact:

\[
  \int_0^1X_{Q_0,m,N}(\alpha)^2\,d\alpha=8R_2(m,N),
\tag{5.12}
\]

\[
  R_2(m,N)=
  \sum_{x,y\in E_0}\gamma_x\gamma_y
    L_H(\beta_x,\beta_y).
\tag{5.13}
\]

For one block, the sum of squared event weights is

\[
  \frac{K_B}{4w_B^2}
  +\frac{2\binom{K_B}{2}}{w_B^2}
  =\frac{K_B^2-3K_B/4}{w_B^2}.
\tag{5.14}
\]

Because `L_H(beta,beta)=H`, the identical-raw-event diagonal is

\[
  D_2(m,N)=H\sum_B
    \frac{K_B^2-3K_B/4}{w_B^2}.
\tag{5.15}
\]

The exact ordered off-diagonal covariance is therefore

\[
  \boxed{\mathfrak C(m,N)=
  \sum_{\substack{x,y\in E_0\\x\ne y}}
    \gamma_x\gamma_y
    \left\lfloor
      \frac{H\gcd(\beta_x,\beta_y)}
           {\max(\beta_x,\beta_y)}
    \right\rfloor.}
\tag{5.16}
\]

This is an ordered sum. There is no missing factor two. It includes every
cross-block and cross-type collision.

## 6. Exhaustive channel partition

Assign every double event to the equal-start event set. For pair events, use
the two literal primitive starts:

\[
\begin{aligned}
  E_{=}&=\{J(B,p)\}
    \cup\{M(B,p,q),P(B,p,q):n_p=n_q\},\\
  E_{\ne}&=\{M(B,p,q),P(B,p,q):n_p\ne n_q\}.
\end{aligned}
\tag{6.1}
\]

These sets are disjoint and exhaust `E_0`. For
`sigma,tau in {=,not equal}`, define

\[
  \mathfrak C_{\sigma\tau}(m,N)=
  \sum_{\substack{x\in E_\sigma,\ y\in E_\tau\\x\ne y}}
    \gamma_x\gamma_yL_H(\beta_x,\beta_y).
\tag{6.2}
\]

Every summand of (5.16) belongs to exactly one of the four sectors, so

\[
  \boxed{\mathfrak C=
    \mathfrak C_{==}+\mathfrak C_{=\ne}
    +\mathfrak C_{\ne=}+\mathfrak C_{\ne\ne}.}
\tag{6.3}
\]

Symmetry of `L_H` gives

\[
  \mathfrak C_{=\ne}=\mathfrak C_{\ne=},\qquad
  \mathfrak C=\mathfrak C_{==}
    +2\mathfrak C_{=\ne}+\mathfrak C_{\ne\ne}.
\tag{6.4}
\]

Within `C_(==)`, the three event types give the nine ordered subchannels

\[
  JJ,JM,JP,MJ,MM,MP,PJ,PM,PP.
\tag{6.5}
\]

The estimate below treats all nine simultaneously and does not discard
cross-type coincidences.

## 7. Complete equal-start arithmetic classification

For a double event from `p=(r,n)`, put `e=n+r`. For an equal-start pair,
write its distinct lags as `r<s` and put

\[
  t=n+r,\qquad e=n+s.
\tag{7.1}
\]

Both `t` and `e` lie in the same canonical block.

### 7.1 Doubles

\[
  \beta_J=2d_{r,n}=2\cdot10^n(10^r-1)
          =2(10^e-10^n).
\tag{7.2}
\]

Since the repunit is odd and prime to five,

\[
  (v_2(\beta_J),v_5(\beta_J),v_{10}(\beta_J))
  =(n+1,n,n).
\tag{7.3}
\]

### 7.2 Equal-start differences

\[
\begin{aligned}
  \beta_M
  &=10^n(10^s-10^r)\\
  &=10^t(10^{e-t}-1)
   =10^tR_{e-t}=10^e-10^t.
\end{aligned}
\tag{7.4}
\]

Thus every equal-start difference is exactly another primitive repunit
frequency, and

\[
  (v_2(\beta_M),v_5(\beta_M),v_{10}(\beta_M))=(t,t,t).
\tag{7.5}
\]

For fixed endpoints `t<e` lying in one block, this numerical base frequency
occurs exactly

\[
  \mu(t)=t-m+1
\tag{7.6}
\]

times: choose the common start `n=0,...,t-m`, then set `r=t-n` and
`s=e-n`. This is the complete repeated-frequency multiplicity in the
equal-start base-event set.

### 7.3 Equal-start sums

\[
  \beta_P=10^n(10^r+10^s-2)
         =10^e+10^t-2\cdot10^n.
\tag{7.7}
\]

Its exact valuations are

\[
  (v_2(\beta_P),v_5(\beta_P),v_{10}(\beta_P))
  =(n+c(r,s),n,n),
\tag{7.8}
\]

where

\[
  c(r,s)=
  \begin{cases}
    1,&r\ge2,\\
    2,&r=1,\ s=2,\\
    4,&r=1,\ s=3,\\
    3,&r=1,\ s\ge4.
  \end{cases}
\tag{7.9}
\]

Indeed, the parenthesis in (7.7) is `3 mod 5`. For `r>=2` it is `2 mod 4`.
For `r=1` it equals `10^s+8`, giving the final three cases by direct division
by powers of two.

### 7.4 Base equalities and derived collisions

Two doubles agree only when their primitive parameters agree. Two sums agree
only when their common start and unordered lag pair agree. Two differences
agree exactly when `(t,e)` agrees, with multiplicity (7.6).

A difference cannot equal a double or sum because its 2-adic and 5-adic
valuations are equal, whereas the other two types have strictly larger
2-adic valuation. A double cannot equal a sum: 5-adic valuation first forces
the same common start, after which equality would give

\[
  2\cdot10^q=10^r+10^s,\qquad r<s.
\tag{7.10}
\]

The 5-adic valuation of the right side is `r`, so `q=r`, and then
`2=1+10^(s-r)`, impossible.

This classifies base equality only. Distinct base frequencies of any two
types may still collide after multiplication by `h,h'<=H`; all such derived
collisions remain in the exact gcd count (5.10).

## 8. Equal-start covariance estimate

### 8.1 Two decay coordinates

For every equal-start event `x`, let

\[
  e(x)=\text{its upper endpoint},\qquad
  u(x)=v_5(\beta_x).
\tag{8.1}
\]

Equations (7.2), (7.4), and (7.7), together with `m>=1`, give the uniform
size bounds

\[
  \frac9{10}10^{e(x)}\le\beta_x\le2\cdot10^{e(x)}.
\tag{8.2}
\]

For example, an equal-start difference is `10^e-10^t` with `t<=e-1`;
a double is `2(10^e-10^n)`; and a sum is
`10^e+10^t-2*10^n`, where `10^t>=10*10^n`.

For equal-start events `x,y`, put

\[
  \rho(x,y)=\frac{\gcd(\beta_x,\beta_y)}
                  {\max(\beta_x,\beta_y)}.
\tag{8.3}
\]

The size bounds imply

\[
  \rho(x,y)\le\frac{20}{9}
    10^{-|e(x)-e(y)|}.
\tag{8.4}
\]

The exact 5-adic valuations independently imply

\[
  \rho(x,y)\le5^{-|u(x)-u(y)|}.
\tag{8.5}
\]

To check (8.5), suppose `u(x)<=u(y)`. After removing `5^u(x)` from the gcd,
the remaining gcd is prime to five and divides the prime-to-five part of
`beta_y`; hence it is at most `beta_y/5^u(y)`. Division by the maximum gives
(8.5).

Taking the geometric mean of (8.4) and (8.5), and using
`sqrt(20/9)<3/2`, yields

\[
  \boxed{L_H(\beta_x,\beta_y)\le
  \frac32H\,10^{-|e(x)-e(y)|/2}
               5^{-|u(x)-u(y)|/2}.}
\tag{8.6}
\]

This holds uniformly in all nine ordered type channels and across blocks.

### 8.2 Exact cell masses

For integers `e,u>=0`, define the total equal-start weight in one cell by

\[
  z_{e,u}=\sum_{\substack{x\in E_=\\e(x)=e,\ u(x)=u}}\gamma_x.
\tag{8.7}
\]

The canonical blocks are disjoint, so the upper endpoint `e` determines its
block. If `e in [a,b)`, write

\[
  z_{e,u}=J_{e,u}+M_{e,u}+P_{e,u}.
\tag{8.8}
\]

The arithmetic classification gives the exact formulas

\[
  J_{e,u}=\frac1{2w_B}
    \mathbf1_{\{u+m\le e\}},
\tag{8.9}
\]

\[
  M_{e,u}=\frac{u-m+1}{w_B}
    \mathbf1_{\{m\le u,\ a\le u<e<b\}},
\tag{8.10}
\]

and

\[
\begin{aligned}
  P_{e,u}&=\frac{c_B(e,u)}{w_B},\\
  c_B(e,u)&=
  |\{t\in\mathbb N:\max(a,u+m)\le t<e\}|.
\end{aligned}
\tag{8.11}
\]

Formula (8.10) retains all `u-m+1` occurrences of the primitive repunit
frequency (7.4). Formula (8.11) retains every equal-start sum.

### 8.3 Canonical-block geometry

The literal decreasing-binary construction of `translatedCanonicalBlocks N`
gives consecutive positive-length blocks partitioning `[1,N)`. Therefore

\[
  \sum_B L_B=N-1.
\tag{8.12}
\]

For completeness, let `P` be the first and largest binary block length.
The binary expansion of `N-1` gives

\[
  P\le N-1<2P.
\tag{8.13}
\]

The first block starts at one, so its endpoint sum is `P+2>=N/2`. Every
later block starts beyond the first block and has still larger endpoint sum.
Thus every canonical block satisfies

\[
  a_B+b_B\ge\frac N2.
\tag{8.14}
\]

This also follows directly by induction through `dyadicPartitionFrom`; no
probabilistic or arithmetic input is involved.

T90 identifies the exact record cardinality as `2K_B`. Combining this with
T87's `blockRecordMass_le_width` gives

\[
  \frac{2K_B}{w_B}\le w_B,
  \qquad K_B\le\frac{w_B^2}{2}.
\tag{8.15}
\]

### 8.4 Cell square mass

For doubles, every core occupies one cell. Equation (8.15) gives

\[
\begin{aligned}
  \sum_{e,u}J_{e,u}^2
  &=\sum_B\frac{K_B}{4w_B^2}\\
  &\le\frac18|\mathcal B_N|
  \le\frac N8\le\frac{N^2}{8}.
\end{aligned}
\tag{8.16}
\]

For differences, `u-m+1<=N`, there are at most `L_B^2/2` pairs `u<e` in a
block, and `w_B^2=L_B(a_B+b_B)`. Hence (8.14) gives

\[
\begin{aligned}
  \sum_{e,u}M_{e,u}^2
  &\le\sum_B\frac{N^2L_B^2}{2w_B^2}\\
  &\le\sum_BNL_B\le N^2.
\end{aligned}
\tag{8.17}
\]

For sums, `c_B(e,u)<=L_B`, so `c_B(e,u)^2<=L_B c_B(e,u)`. For each pair
`t<e` in the block there are at most `N` possible starts `u`. Therefore

\[
  \sum_{e,u}c_B(e,u)\le\frac{NL_B^2}{2}
\tag{8.18}
\]

and

\[
\begin{aligned}
  \sum_{e,u}P_{e,u}^2
  &\le\sum_B\frac{NL_B^3}{2w_B^2}\\
  &\le\sum_BL_B^2
  \le\left(\sum_BL_B\right)^2\le N^2.
\end{aligned}
\tag{8.19}
\]

Using `(a+b+c)^2<=3(a^2+b^2+c^2)` in every cell, (8.16)-(8.19) give the
explicit square-mass estimate

\[
  \boxed{\sum_{e,u}z_{e,u}^2\le\frac{51}{8}N^2.}
\tag{8.20}
\]

### 8.5 Schur summation

Put

\[
  q=10^{-1/2},\qquad r=5^{-1/2}.
\tag{8.21}
\]

The two-dimensional kernel has mass

\[
\begin{aligned}
  \sum_{i,j\in\mathbb Z}q^{|i|}r^{|j|}
  &=\frac{1+q}{1-q}\frac{1+r}{1-r}\\
  &<2\cdot3=6.
\end{aligned}
\tag{8.22}
\]

Here `q<1/3` and `r<1/2`. For nonnegative cell masses, the elementary
inequality `2ab<=a^2+b^2` gives

\[
  \sum_{\xi,\eta}z_\xi z_\eta K(\xi-\eta)
  \le\|K\|_1\sum_\xi z_\xi^2.
\tag{8.23}
\]

Apply (8.6), group by cells, and temporarily include the nonnegative
identical-event diagonal. Equations (8.20)-(8.23) yield

\[
\begin{aligned}
  \mathfrak C_{==}(m,N)
  &\le\frac32H\cdot6\sum_{e,u}z_{e,u}^2\\
  &\le\frac{459}{8}HN^2\\
  &\le58HN^2.
\end{aligned}
\tag{8.24}
\]

Thus the complete ordered equal-start sector, including every one of the nine
type channels, every cross-block pair, every repeated primitive-repunit
frequency, and every derived multiplier collision, satisfies

\[
  \boxed{\mathfrak C_{==}(m,N)\le58\cdot10^mN^2.}
\tag{ES}
\]

## 9. Critical aggregate and the narrower frontier

Define the literal inclusive critical set

\[
  \mathcal C_m=\{N\in\mathbb N:1\le N,\ H\le N^2\le2H\}.
\tag{9.1}
\]

Every critical `N` is below `2 sqrt(H)`, so

\[
  |\mathcal C_m|\le2\sqrt H.
\tag{9.2}
\]

Dividing (ES) by `N^2` and summing gives

\[
\begin{aligned}
  \sum_{N\in\mathcal C_m}
    \frac{\mathfrak C_{==}(m,N)}{N^2}
  &\le116H^{3/2}\\
  &\le116H^{7/4}.
\end{aligned}
\tag{9.3}
\]

Define the remaining unequal-start covariance by

\[
  \mathfrak U(m,N)=
    \mathfrak C_{=\ne}(m,N)+
    \mathfrak C_{\ne=}(m,N)+
    \mathfrak C_{\ne\ne}(m,N)
  =2\mathfrak C_{=\ne}(m,N)+\mathfrak C_{\ne\ne}(m,N).
\tag{9.4}
\]

The complete unresolved frontier is now the single displayed inequality

\[
\boxed{
\begin{aligned}
  (\mathrm{UCOV}_{1/4})\qquad
  \exists C_U\ge0\ \forall m\ge1,\qquad
  \sum_{N\in\mathcal C_m}
    \frac{\mathfrak U(m,N)}{N^2}
  \le C_UH^{7/4},\qquad H=10^m.
\end{aligned}}
\tag{9.5}
\]

This is strictly narrower than the total covariance inequality: its summation
domain omits every pair whose two base events are equal-start, and that entire
omitted sector has already been bounded in (ES). It retains exactly the two
mixed ordered sectors and the unequal/unequal sector. No event can fall
outside (9.3) and (9.5) because of the exhaustive partition (6.3).

If (9.5) is proved, then (6.4) and (9.3) give the total covariance estimate

\[
  \sum_{N\in\mathcal C_m}
    \frac{\mathfrak C(m,N)}{N^2}
  \le(116+C_U)H^{7/4}.
\tag{9.6}
\]

Thus the explicit total constant would be `C_0=116+C_U`.

## 10. Conditional eventual consequence and honest stopping point

This section records the consequence of (9.5); it does not assume or prove
(9.5).

From (8.15), (5.15), and the telescoping identity
`sum_B w_B^2=N^2-1`,

\[
  0\le D_2(m,N)\le\frac H4(N^2-1).
\tag{10.1}
\]

For the bad event

\[
  \mathcal E_m=\{\alpha\in[0,1):
    \exists N\in\mathcal C_m,\ X_{0,m,N}(\alpha)>Z_{m,N}\},
\tag{10.2}
\]

the lower critical endpoint gives `Z_(m,N)>=2HN`. Chebyshev's inequality,
(5.12), and a finite union bound therefore give

\[
  \lambda(\mathcal E_m)
  \le\frac2{H^2}\sum_{N\in\mathcal C_m}
    \frac{D_2(m,N)+\mathfrak C(m,N)}{N^2}.
\tag{10.3}
\]

Under (9.5), equations (9.6), (10.1), and (9.2) imply

\[
  \lambda(\mathcal E_m)
  \le H^{-1/2}+2(116+C_U)H^{-1/4}.
\tag{10.4}
\]

The sum over `m` converges because `H=10^m`. The first Borel-Cantelli lemma
would then give

\[
\begin{aligned}
  \lambda\text{-a.e. }\alpha\in[0,1),\quad
  \exists m_0(\alpha)\quad\forall m\ge m_0(\alpha)\quad
  \forall N\in\mathcal C_m\quad\forall Q_0\in\mathbb N,\\
  X_{Q_0,m,N}(\alpha)\le Z_{m,N}.
\end{aligned}
\tag{10.5}
\]

This would be (EV) with `B_alpha=1`. The independence of `Q0` follows only
from the T87 audit and does not alter its position in (10.5).

The unconditional stopping point is earlier: (ES) and (9.3) are proved in
this note, while `(UCOV_(1/4))` is a `conjecture`. Hence the eventual
almost-everywhere assertion is not claimed proved or refuted.

## 11. Skeptic replay checklist

| feature | retained form |
|---|---|
| sibling | eventual variable-phase residual A12, not canonical fixed pi |
| phase | `cos(2 pi alpha h d)` only |
| positive scales | `1<=m`, `1<=N` |
| critical band | `10^m<=N^2<=2*10^m`, both endpoints included |
| canonical blocks | every block in `translatedCanonicalBlocks N` |
| core | `0<r`, `m<=r`, `a_B<=n+r<b_B` |
| exclusion | `(mu,c)=(8,1)`; none survive; arbitrary `Q0` retained |
| orientations | both Boolean orientations with signs `-d,+d` |
| frequency | every `h=1,...,10^m`, inclusive |
| width | `sqrt(b_B^2-a_B^2)` literally |
| square factor | `4`, retaining all ordered sign products |
| covariance | exact ordered formula (5.16), no extra factor two |
| partition | four exhaustive sectors in (6.3) |
| equal-start types | all nine ordered `J/M/P` type channels |
| valuation | exact `v_2`, `v_5`, and `v_10` in (7.3), (7.5), (7.8) |
| repunit resonance | exact frequency and multiplicity (7.4)-(7.6) |
| equal-start bound | `C_(==)(m,N)<=58*10^m*N^2` |
| aggregate bound | constant `116` in (9.3) |
| narrower gap | only mixed and unequal-start sectors in (9.5) |
| eventual order | `alpha`, then `B_alpha,m0`, then `m,N,Q0` |
| fixed pi | no conclusion |
| C1, C2, C3 | no conclusion |
