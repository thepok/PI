# T17: sparse periodic islands give a sibling barrier

Status: `proof sketch` (complete rigorous prose proof, not machine-checked).

## 1. Provenance and claim boundary

The immutable local question is vendored as `CANONICAL_STATEMENT.txt`. Its
SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

It asks about the fixed decimal expansion of pi. The theorem below instead
constructs a different real number `alpha`. It is a **sibling barrier
theorem**: the condition `mu(alpha)<8` alone does not force the analogous
long-lag collision estimate for arbitrary decimal reals. It is not evidence
that C1 fails for pi, and it proves no statement about the digits of pi.

The source-pinned external input is the Jarnik--Besicovitch exceptional-set
theorem recorded in `SOURCE_PIN.md`. No unverified claim from an earlier
program note is used as a premise.

## 2. Normalized sibling statement and conventions

Let `D={0,1,...,9}` and let `d=(d_n)_(n>=0)` be a zero-based decimal digit
sequence. Put

\[
  x(d)=\sum_{n=0}^{\infty}d_n10^{-(n+1)}\in[0,1].       \tag{2.1}
\]

For integers `i>=0` and `m>=1`, define

\[
 B_d(i,m)=(d_i,d_{i+1},\ldots,d_{i+m-1}).               \tag{2.2}
\]

For `N>=1`, define the exact ordered long-lag count

\[
 R_d(m,N)=\#\{(i,j)\in\{0,\ldots,N-1\}^2:
       |i-j|\ge m,\ B_d(i,m)=B_d(j,m)\}.                 \tag{2.3}
\]

Pairs are ordered, the diagonal and overlapping starts are excluded, and
blocks may use digits beyond start `N-1`, exactly as in the canonical
definition. For an irrational `x`, its decimal expansion is unique; `R_x`
means (2.3) for that expansion.

The sibling analogue of C1 is

\[
 \forall s\in(0,1)\ \exists C_s\ge1\ \forall m,N\ge1,
 \quad R_x(m,N)\le C_s\bigl(N+N^2 10^{-sm}\bigr).        \tag{2.4}
\]

The constants in (2.4) are selected before `m,N`. We prove the following.

**Theorem 2.1 (sibling barrier).** There is an irrational real number
`alpha in [0,1]` with irrationality exponent `mu(alpha)<8` for which (2.4)
is false. More precisely, for `s=1/2` there are integer sequences `m_k,N_k`
such that

\[
 \frac{R_\alpha(m_k,N_k)}
 {N_k+N_k^2 10^{-m_k/2}}\longrightarrow\infty.          \tag{2.5}
\]

The only quantifier issue not inherited from the canonical statement is the
choice of a decimal representative. It is harmless because the selected
`alpha` is irrational. The construction first works symbolically and only
then selects `alpha`.

## 3. Integer schedule and disjoint islands

Define positive integers recursively by

\[
 r_1=10,\qquad r_{k+1}=10^{4r_k},                       \tag{3.1}
\]

and set

\[
 A_k=10^{4r_k}=r_{k+1},\qquad
 m_k=12r_k,\qquad L_k=10^{3r_k},\qquad N_k=A_k+L_k.     \tag{3.2}
\]

The `k`-th island is the zero-based integer interval

\[
 I_k=\{A_k,A_k+1,\ldots,A_k+L_k-1\}.                   \tag{3.3}
\]

All quantities are integers. Since `r_k>=10`, we have
`m_k=12r_k<L_k=10^(3r_k)`. Also

\[
 A_k+L_k<2A_k<10^{4A_k}=A_{k+1}.                       \tag{3.4}
\]

For the second inequality, `A_k>=1` and `2A_k<10^(4A_k)` are immediate, for
example from `2A_k<=2^(A_k+1)<10^(4A_k)`. Thus the islands are strictly
ordered and pairwise disjoint. Notice also that `r_k` is strictly increasing
and tends to infinity.

## 4. The closed decimal set

Let `X` be the set of all digit sequences `d in D^N` satisfying, for every
`k` and every integer `0<=t<L_k`,

\[
 d_{A_k+t}=d_{A_k+(t\bmod m_k)}.                        \tag{4.1}
\]

Thus the first `m_k` digits in island `I_k` are arbitrary and that one
length-`m_k` word is repeated periodically across the entire island. Formula
(4.1), including a possibly incomplete last repetition, is the precise
meaning of "throughout the island."

Each equality in (4.1) defines a clopen subset of the compact product space
`D^N`. Hence `X`, their intersection, is closed and compact. It is nonempty:
choose all unconstrained digits arbitrarily and propagate them using (4.1).
The disjointness in (3.4) makes these prescriptions consistent.

The continuous decimal map (2.1) sends `X` to a compact, hence closed, set

\[
                         K=x(X)\subset[0,1].             \tag{4.2}
\]

## 5. Nonoverlapping repeated starts and ordered collisions

Put

\[
                         M_k=\lfloor L_k/m_k\rfloor.     \tag{5.1}
\]

Because `L_k/m_k>=2`, the elementary bound `floor(y)>=y/2` for `y>=2` gives

\[
                    M_k\ge {L_k\over2m_k}\quad\hbox{and}\quad M_k\ge2.
                                                                    \tag{5.2}
\]

Consider the `M_k` starts

\[
             S_k=\{A_k+t m_k:0\le t<M_k\}.              \tag{5.3}
\]

They all lie in `{0,...,N_k-1}` because
`A_k+t m_k<A_k+M_km_k<=A_k+L_k=N_k`. The whole block of
length `m_k` from each such start lies in `I_k`. By (4.1), all these blocks
equal the first period:

\[
 B_d(A_k+t m_k,m_k)=B_d(A_k,m_k).                       \tag{5.4}
\]

For distinct `t,u`, the lag is `m_k|t-u|>=m_k`, so the two blocks are
nonoverlapping under the exact weak lag convention. Every ordered pair of
distinct members of `S_k` is therefore counted. For every `d in X`,

\[
 \begin{aligned}
 R_d(m_k,N_k)
   &\ge M_k(M_k-1)\\
   &\ge \tfrac12M_k^2
    \ge {L_k^2\over8m_k^2}
     ={10^{6r_k}\over1152r_k^2}.                        \tag{5.5}
 \end{aligned}
\]

This is an ordered lower bound; no unrecorded factor of two is needed.

## 6. Additive-N and exponential-term comparison

Since `L_k<A_k`,

\[
 N_k=A_k+L_k\le2A_k=2\cdot10^{4r_k}.                   \tag{6.1}
\]

At `s=1/2`, the selected block length gives `s m_k=6r_k`. Hence

\[
 N_k^2 10^{-m_k/2}
 \le4\cdot10^{8r_k}10^{-6r_k}
 =4\cdot10^{2r_k}.                                     \tag{6.2}
\]

Combining (6.1), (6.2), and `10^(2r_k)<=10^(4r_k)`,

\[
 N_k+N_k^2 10^{-m_k/2}\le6\cdot10^{4r_k}.              \tag{6.3}
\]

Equations (5.5)--(6.3) give the explicit normalized lower bound

\[
 \frac{R_d(m_k,N_k)}{N_k+N_k^2 10^{-m_k/2}}
 \ge {10^{2r_k}\over6912r_k^2}.                        \tag{6.4}
\]

The right side tends to infinity. Indeed, for integer `r>=1`, the ratio of
`10^(2(r+1))/(r+1)^2` to `10^(2r)/r^2` is
`100(r/(r+1))^2>=25`; and `r_k` tends to infinity. Thus (2.5) holds for every
irrational member of `K`. In particular, no constant `C_(1/2)` can satisfy
(2.4) for such a member.

## 7. Zero-density constraint count

The genuinely dependent coordinates of island `k` form

\[
 C_k=\{A_k+m_k,\ldots,A_k+L_k-1\};                     \tag{7.1}
\]

the first `m_k` coordinates are free. Let `C=union_k C_k` and

\[
 c(n)=\#(C\cap\{0,\ldots,n-1\}).                       \tag{7.2}
\]

We use the coarser bound `#C_k<=L_k`. Since `r_(k+1)>r_k`,
`L_(k+1)/L_k=10^(3(r_(k+1)-r_k))>=1000`, and in particular

\[
                         \sum_{h=1}^kL_h\le2L_k.         \tag{7.3}
\]

This follows directly by induction: the next term is at least twice the
previous partial-sum bound.

For `A_k<=n<A_(k+1)`, only islands through `k` can contribute, so

\[
 0\le {c(n)\over n}
 \le {\sum_{h=1}^kL_h\over A_k}
 \le {2L_k\over A_k}=2\cdot10^{-r_k}.                  \tag{7.4}
\]

As `n` tends to infinity, the applicable `k` tends to infinity. Therefore

\[
                             c(n)/n\longrightarrow0.     \tag{7.5}
\]

This estimate is uniform even while `n` lies inside an island; measuring
against its large starting position `A_k` is essential.

## 8. Hausdorff dimension one

Let `F=N\C` be the free-coordinate set. For `n in C_k`, let

\[
 \rho(n)=A_k+((n-A_k)\bmod m_k),                        \tag{8.1}
\]

and put `rho(n)=n` for `n in F`. The value in (8.1) belongs to the first
period of `I_k`, hence to `F`. Every assignment of digits to `F` extends
uniquely to a member of `X` by `d_n=d_(rho(n))`.

Give the free digits independent uniform distributions on `D`, extend them
as above, and push the resulting probability measure through (2.1) to a
measure `nu` supported on `K`. Among the first `n` coordinates there are
exactly

\[
                            f(n)=n-c(n)                  \tag{8.2}
\]

free choices. Consequently every compatible decimal cylinder of level `n`
has measure `10^(-f(n))`; incompatible cylinders have measure zero.

For completeness, decimal endpoints cause no loss here. The measure of a
single digit sequence is zero because `f(n)` tends to infinity. Thus the
countable set of decimal grid endpoints has `nu`-measure zero. An interval
`J` of length `ell` with

\[
                 10^{-(n+1)}<\ell\le10^{-n}             \tag{8.3}
\]

meets at most three level-`n` decimal grid intervals, up to null endpoints.
Therefore

\[
                             \nu(J)\le3\,10^{-f(n)}.      \tag{8.4}
\]

Fix any real `0<t<1`. By (7.5), `f(n)/n` tends to `1`, so for all sufficiently
large `n`, `f(n)>=tn`. From (8.3)--(8.4),

\[
 \nu(J)\le3\,10^{-tn}\le3\,10^t\ell^t                 \tag{8.5}
\]

for every sufficiently short interval `J`. Enlarging the constant covers the
remaining interval lengths. The mass-distribution argument is immediate: if
`K` is covered by sufficiently short intervals `J_i`, then

\[
 1=\nu(K)\le\sum_i\nu(J_i)\le C_t\sum_i|J_i|^t,
\]

so the `t`-dimensional Hausdorff content of `K` is positive. Hence
`dim_H K>=t`. Since this holds for every `t<1` and `K subset [0,1]`,

\[
                              \dim_H K=1.                \tag{8.6}
\]

This proves dimension one rather than merely upper box dimension one.

## 9. Source-pinned exceptional set and selection of alpha

For a real `x`, use the source's convention

\[
 \mu(x)=\sup\{z:\ 0<|x-p/q|<q^{-z}
       \text{ for infinitely many }(p,q)\in\mathbb Z^2,
       \ q>0\}.                                         \tag{9.1}
\]

The retained Becher--Reimann--Slaman source states the classical
Jarnik--Besicovitch theorem

\[
 \dim_H\{x\in\mathbb R:\mu(x)\ge a\}=2/a              \tag{9.2}
\]

for the relevant range `a>=2`. Its exact locator, immutable arXiv version,
URL, and SHA-256 are in `SOURCE_PIN.md`. Taking `a=8` gives

\[
 \dim_H E_8=1/4,
 \qquad E_8=\{x\in\mathbb R:\mu(x)\ge8\}.              \tag{9.3}
\]

The endpoint `>=8` in the cited statement is important: no identification
with a fixed-exponent limsup set is being made.

The rationals `Q` are countable and have Hausdorff dimension zero. If
`K subset E_8 union Q`, countable stability of Hausdorff dimension would give

\[
 \dim_HK\le\max(\dim_HE_8,\dim_HQ)=1/4,
\]

contrary to (8.6). Choose

\[
                         \alpha\in K\setminus(E_8\cup Q). \tag{9.4}
\]

Then `alpha` is irrational and `mu(alpha)<8`. There is a sequence `d in X`
with `x(d)=alpha`. Irrationality makes `d` the unique decimal expansion of
`alpha`, so Sections 5--6 apply to `R_alpha` and prove (2.5). This completes
Theorem 2.1.

## 10. What has and has not been shown

The construction proves that an irrationality-exponent upper restriction
below eight, by itself, cannot imply the long-lag collision estimate for all
decimal reals. It does not contradict the published irrationality bound for
pi, does not transfer the constructed digit islands to pi, and does not prove
or disprove canonical C1. Any fixed-pi proof still may use additional
orbit-specific arithmetic information unavailable for the constructed
`alpha`.
