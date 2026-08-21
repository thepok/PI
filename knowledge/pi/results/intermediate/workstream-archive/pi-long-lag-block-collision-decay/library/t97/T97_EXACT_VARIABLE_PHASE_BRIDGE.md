# T97: Exact variable-phase bridge from T90 to T31 CROSS

Claim labels:

- `machine-checked`: the declarations in `T97VariablePhaseBridge.lean` and the
  imported T31/T87/T90 declarations cited below.
- `proof sketch`: the fully explicit finite covariance and Borel-Cantelli
  derivation in Sections 7-10. It uses only the cited machine-checked
  interfaces and elementary finite-sum and measure arguments written out here.

## 1. Provenance and scope

- Canonical local statement: `CANONICAL_STATEMENT.txt`.
- Verified canonical SHA-256:
  `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`.
- Original external source URL: none. The canonical statement records that the
  system formulated the question on 2026-07-23.
- This artifact concerns only the Lebesgue-variable-phase version of T29's
  residual sparse-Fourier sibling A12.
- It states no conclusion for fixed `pi`, C1, C2, C3, or the canonical
  long-lag collision count.

The T95 and T96 notes are unverified `proof sketch` motivation. No claim from
either note is a premise here. All event definitions and calculations needed
below are repeated and checked independently against the kernel-checked
T31/T87/T90 interfaces.

## 2. Normalized target and quantifiers

Let `lambda` be Lebesgue measure restricted to `[0,1)`, so
`lambda([0,1))=1`. This is exactly T18's `phaseMeasure`. For `m>=1`, put

\[
  H=10^m.
\tag{2.1}
\]

For each positive `N` in the inclusive critical band

\[
  H\le N^2\le2H,
\tag{2.2}
\]

and each `Q0` in the natural numbers, define

\[
  X_{Q_0,m,N}(\alpha)
  =\operatorname{widthWeightedSquareFunction}(8,1,Q_0,m,N,\alpha)
   -\operatorname{recordDiagonal}(Q_0,m,N).
\tag{2.3}
\]

The phase replacement is only

\[
  \cos(2\pi^2hd)\longmapsto\cos(2\pi\alpha hd),
  \qquad \alpha\in[0,1).
\tag{2.4}
\]

The target normalization is

\[
  Z_{m,N}=H\left(N+\frac{N^2}{\sqrt H}\right).
\tag{2.5}
\]

The conclusion proved by the route below has the exact order

\[
\lambda\text{-a.e. }\alpha,\quad
\exists m_0(\alpha)\quad
\forall m\ge m_0(\alpha)\quad
\forall N\in\mathbb N\quad
\bigl(1\le N\ \wedge\ H\le N^2\le2H\bigr)
\Longrightarrow
\forall Q_0\in\mathbb N,\quad
X_{Q_0,m,N}(\alpha)\le Z_{m,N}.
\tag{2.6}
\]

Thus the eventual constant-relaxed formulation holds with the explicit choice
`B_alpha=1`. The assertion is one-sided; no absolute-value conclusion is
claimed.

### Quantifier and convention ambiguities resolved

1. Both critical-band endpoints in (2.2) are included.
2. Every multiplier `h=1,...,H` is included; `h=0` is excluded.
3. `Q0` remains after `m,N` in (2.6). Independence of `Q0` is proved, not
   assumed.
4. Every T29 canonical block is retained with weak left and strict right
   endpoint.
5. Both Boolean orientations and both signs are retained before centering.
6. The literal width is always
   `sqrt(B.finish^2-B.start^2)`.
7. Event occurrences are counted with multiplicity. Equal numerical base
   frequencies are never silently identified.

## 3. Machine-checked interfaces

The following imported declarations are established inputs.

### T31

1. `blockOffDiagonal_eq_orient_image` and
   `orientPositiveDifference_injOn_block` identify every ordered
   off-diagonal pair with one sign choice and one strict positive signed
   difference.
2. `blockPhaseSum_norm_sq_sub_card` gives the exact centered expansion over
   `blockPositiveDifferenceDomain`.
3. `integral_centeredWidthWeightedSquareFunction_sq` gives the exact finite
   resonance sum, including the factor `2`.
4. `crossBlockWeightedGCD_le` gives
   \[
     \operatorname{CROSS}\le
     470226400N^2\log(2N).
   \tag{3.1}
   \]
5. `integral_centeredWidthWeightedSquareFunction_sq_le` combines the exact
   resonance count with (3.1):
   \[
     \int X^2\,d\lambda\le
     940452800HN^2\log(2N).
   \tag{3.2}
   \]

### T87

1. `not_arithmeticExcluded_eight_one` proves that no arithmetic exclusion
   survives at `(mu,c)=(8,1)`, for arbitrary `Q0`.
2. `blockRecordDomain_both_orientations_eight_one` retains both orientations,
   the signs `-d,+d`, and the exact half-open block.
3. `blockOrderedDomain_eq_blockRecordDomain` identifies T31's endpoint-filtered
   domain with the literal T90 record domain on each canonical block.
4. `inclusiveFrequencies_card_exact` proves that the multiplier cardinality is
   exactly `H=10^m`.
5. `recordDiagonal_exact_formula_literal` fixes the exact diagonal and widths.

### T90

1. `mem_blockCoreDomain_literal` gives
   \[
     D_{m,B}=\{(r,n):0<r,\ m\le r,\ B.start\le n+r<B.finish\}.
   \tag{3.3}
   \]
2. `blockRecordDomain_eight_one_eq_orientations` identifies the record domain
   with `Bool x D_(m,B)`.
3. `blockCoreDomain_orientation_exclusion_audit` exposes both signs and the
   eliminated arithmetic exclusion.
4. `recordDiagonal_eq_coreCard` fixes the diagonal factor `2H` after
   quotienting orientations.

T90's unproved proposition `CORR_pi` is not used.

## 4. New machine-checked bridge

The file `T97VariablePhaseBridge.lean` proves the following.

1. `two_orientations_variablePhase_eq_cosine` directly establishes
   \[
     e^{-2\pi i\alpha hd}+e^{2\pi i\alpha hd}
     =2\cos(2\pi\alpha hd).
   \tag{4.1}
   \]
   It does not specialize or repurpose T90's fixed-pi identity.
2. `widthWeightedSquareFunction_eight_one_variable_eq_coreSum` proves
   \[
     W_{m,N}(\alpha)
      =4\sum_B\frac1{w_B}\sum_{h=1}^{H}
        \left(\sum_{p\in D_{m,B}}
          \cos(2\pi\alpha h d_p)\right)^2,
   \tag{4.2}
   \]
   with
   \[
     d_{(r,n)}=10^n(10^r-1),\qquad
     w_B=\sqrt{B.finish^2-B.start^2}.
   \tag{4.3}
   \]
3. `variableCenteredCriticalRemainder_literal` proves the fully unfolded
   centered formula, with outer factor `4`, diagonal factor `2H`, all blocks,
   all inclusive multipliers, and every literal width.
4. `variableCenteredCriticalRemainder_eq_T31` proves the exact identity
   \[
     X_{Q_0,m,N}(\alpha)
      =\operatorname{centeredWidthWeightedSquareFunction}
        (8,1,Q_0,m,N,\alpha).
   \tag{4.4}
   \]
5. `variableCenteredCriticalRemainder_Q0_independent` proves
   \[
     X_{Q_0,m,N}(\alpha)=X_{Q_1,m,N}(\alpha)
   \tag{4.5}
   \]
   for all `Q0,Q1`, after using T87/T90's exact domains.
6. `variableCenteredCriticalRemainder_secondMoment_le` is the direct T31
   corollary (3.2) for the exact observable (2.3).

These declarations compile with only `propext`, `Classical.choice`, and
`Quot.sound`.

## 5. Complete signed-difference occurrence map

Fix one canonical block `B`. Put `K_B=|D_(m,B)|`. Positive lag makes
`p -> d_p` injective: decimal valuation first determines `n`, and then
strict monotonicity of `10^r-1` determines `r`. T87/T90 therefore give the
`2K_B` distinct signed records

\[
  S_B=\{-d_p,+d_p:p\in D_{m,B}\}.
\tag{5.1}
\]

By T31's definition, its positive-difference domain consists of exactly one
ordered representative `(u,v)` with `v<u` for every unordered pair of
distinct elements of `S_B`. There are no diagonal pairs and no second
orientation of the same unordered signed pair.

For one core `p`, the pair is

| T31 ordered pair | positive value | multiplicity |
|---|---:|---:|
| `(+d_p,-d_p)` | `2d_p` | 1 |

For distinct cores, order them by `d_p<d_q`. The four cross-core unordered
signed pairs are exactly

| T31 ordered pair | positive value | collapsed type |
|---|---:|---|
| `(+d_q,+d_p)` | `d_q-d_p` | difference |
| `(-d_p,-d_q)` | `d_q-d_p` | difference |
| `(+d_p,-d_q)` | `d_p+d_q` | sum |
| `(+d_q,-d_p)` | `d_p+d_q` | sum |

This is exhaustive: one same-core pair and four cross-core pairs account for
all unordered pairs in (5.1). Equivalently,

\[
  K_B+4\binom{K_B}{2}=\binom{2K_B}{2}.
\tag{5.2}
\]

The same-core membership and value for every core, including singleton blocks
and a block's maximal core, are machine-checked independently by
`signedDouble_occurrence_and_value`. The four cross-core memberships and all
displayed cross-core values are machine-checked by
`signedDifference_occurrence_map` and
`signedDifference_occurrence_values`.

## 6. Coefficients and every factor

T31's `blockPhaseSum_norm_sq_sub_card` assigns each positive signed-difference
occurrence the pair of phases

\[
  e^{-2\pi i\alpha h\delta}+e^{2\pi i\alpha h\delta}
  =2\cos(2\pi\alpha h\delta).
\tag{6.1}
\]

After division by `w_B`, each T31 occurrence therefore has cosine coefficient
`2/w_B`. Collapse the occurrence map of Section 5 into the following tagged
base events:

| event | base frequency `beta_x` | positive weight `gamma_x` |
|---|---:|---:|
| double `J(B,p)` | `2d_p` | `1/(2w_B)` |
| difference `M(B,p,q)` | `|d_p-d_q|` | `1/w_B` |
| sum `P(B,p,q)` | `d_p+d_q` | `1/w_B` |

Then the coefficients agree exactly:

1. A double has one T31 occurrence, hence coefficient
   `2/w_B=4*(1/(2w_B))`.
2. A difference has two T31 occurrences, hence combined coefficient
   `4/w_B=4*(1/w_B)`.
3. A sum has two T31 occurrences, hence combined coefficient
   `4/w_B=4*(1/w_B)`.

Thus, with `E0` a set of tagged occurrences and not a set of numerical
frequencies,

\[
  X_{Q_0,m,N}(\alpha)
   =4\sum_{x\in E_0}\gamma_x
       \sum_{h=1}^{H}\cos(2\pi\alpha h\beta_x).
\tag{6.2}
\]

For `k>=1`, set

\[
  a_k=\sum_{x\in E_0}\sum_{1\le h\le H\atop h\beta_x=k}\gamma_x.
\tag{6.3}
\]

If instead `b_k` sums T31's uncollapsed occurrence weights `1/w_B`, the
occurrence table gives the exact identity

\[
  b_k=2a_k.
\tag{6.4}
\]

No factor is lost: (6.4) is precisely why T31's factor `2` in the integrated
signed-pair product becomes the factor `8` below.

## 7. Exact resonance and full covariance

For positive integers `u,v`, T31's `resonanceDomain H u v` is literally

\[
  \{(h,k)\in[1,H]^2:hu=kv\}.
\tag{7.1}
\]

Writing `g=gcd(u,v)`, `u=gA`, and `v=gB`, coprimality gives
`(h,k)=(Bt,At)`. Hence its exact cardinality is

\[
  L_H(u,v)=
  \left\lfloor\frac{H\gcd(u,v)}{\max(u,v)}\right\rfloor.
\tag{7.2}
\]

T16's checked kernel is exactly

\[
  \operatorname{gcdKernel}(u,v)=\frac{\gcd(u,v)}{\max(u,v)},
\tag{7.3}
\]

and T18/T31 check `L_H(u,v)<=H*gcdKernel(u,v)`.

Define

\[
  R_2(m,N)=\sum_{k\ge1}a_k^2.
\tag{7.4}
\]

Orthogonality on `[0,1)` and (6.2) give

\[
  \int_0^1X_{Q_0,m,N}(\alpha)^2\,d\alpha=8R_2(m,N).
\tag{7.5}
\]

This is also exactly T31's checked resonance identity: by (6.4), its weighted
ordered resonance sum is `2*sum_k b_k^2=8*sum_k a_k^2`.

Let the raw identical-event diagonal be

\[
  D_2(m,N)=H\sum_B\frac{K_B^2-3K_B/4}{w_B^2},
\tag{7.6}
\]

and define the full ordered off-diagonal covariance

\[
\begin{aligned}
  \mathfrak C(m,N)
  &=R_2(m,N)-D_2(m,N)\\
  &=\sum_{x\ne y}\gamma_x\gamma_y
    \left\lfloor
      \frac{H\gcd(\beta_x,\beta_y)}
           {\max(\beta_x,\beta_y)}
    \right\rfloor.
\end{aligned}
\tag{7.7}
\]

The sum is ordered. No factor two is omitted. Every term is nonnegative, so
`0<=C<=R2`. Dividing (3.2) by eight gives the unconditional full covariance
bound

\[
\boxed{
  0\le\mathfrak C(m,N)\le R_2(m,N)
  \le117556600\,H N^2\log(2N).
}
\tag{7.8}

This includes every equal-start, unequal-start, mixed, cross-type, and
cross-block sector. No T95 `COV` or T96 `UCOV` conjecture remains.

## 8. Explicit aggregate covariance constant

Let

\[
  \mathcal C_m=\{N\in\mathbb N:1\le N,\ H\le N^2\le2H\}.
\tag{8.1}
\]

Every member satisfies `N<2*sqrt(H)`, hence
`|C_m|<=2*sqrt(H)` and `log(2N)<=log(4*sqrt(H))`.

For `m>=1`, the elementary bound

\[
  \log(4\sqrt H)\le2H^{1/4}
\tag{8.2}
\]

has explicit slack. Indeed `log 4<2`, `log 10<3`, and therefore the left side
is below `2+(3/2)m`. Put `q=10^(1/4)`. Since `(7/4)^4<10`, `q>7/4`.
The inequality `2+(3/2)m<=2q^m` holds at `m=1`; its right-minus-left
increment is `2q^m(q-1)-3/2>=2(q-1)-3/2>0`. This proves (8.2) by induction.

Using (7.8), (8.1), and (8.2),

\[
\begin{aligned}
  \sum_{N\in\mathcal C_m}
    \frac{\mathfrak C(m,N)}{N^2}
  &\le117556600\,H\,|\mathcal C_m|\,
      \log(4\sqrt H)\\
  &\le470226400\,H^{7/4}.
\end{aligned}
\tag{8.3}
\]

Thus the full covariance inequality requested by the motivating route holds
unconditionally with the explicit scale-independent constant

\[
  C_0=470226400.
\tag{8.4}
\]

## 9. Explicit maximal tail

For each positive `m`, define the measurable bad event

\[
  \mathcal E_m=\{\alpha\in[0,1):
    \exists N\in\mathcal C_m,\
      X_{0,m,N}(\alpha)>Z_{m,N}\}.
\tag{9.1}
\]

Measurability follows because T31 proves continuity of the centered square
function and the union over `C_m` is finite.

The lower critical endpoint gives `sqrt(H)<=N`, so

\[
  Z_{m,N}=H\left(N+\frac{N^2}{\sqrt H}\right)\ge2HN.
\tag{9.2}
\]

The event `X>Z` is contained in `X^2>=Z^2`. Markov's inequality applied to
the nonnegative function `X^2`, followed by (3.2) and (9.2), gives for each
critical `N`

\[
\begin{aligned}
  \lambda\{X_{0,m,N}>Z_{m,N}\}
  &\le\frac{\int X_{0,m,N}^2\,d\lambda}{Z_{m,N}^2}\\
  &\le\frac{940452800HN^2\log(2N)}{4H^2N^2}\\
  &=235113200\frac{\log(2N)}H.
\end{aligned}
\tag{9.3}
\]

A finite union bound, `|C_m|<=2sqrt(H)`, and (8.2) now give

\[
\boxed{
  \lambda(\mathcal E_m)\le940452800\,H^{-1/4}
  =940452800\,10^{-m/4}.
}
\tag{9.4}
\]

For every positive `M`, the tail is explicitly

\[
\boxed{
  \sum_{m=M}^{\infty}\lambda(\mathcal E_m)
  \le
  \frac{940452800\,10^{-M/4}}{1-10^{-1/4}}.
}
\tag{9.5}

No independence between scales or events is used.

## 10. Borel-Cantelli conclusion

The right side of (9.5) is finite. The first Borel-Cantelli lemma therefore
implies that almost every `alpha` belongs to only finitely many `E_m`. For
such an `alpha`, choose `m0(alpha)` larger than every exceptional scale and at
least one. Then for every `m>=m0(alpha)` and every `N` in the inclusive
critical band,

\[
  X_{0,m,N}(\alpha)\le Z_{m,N}.
\tag{10.1}
\]

The machine-checked `variableCenteredCriticalRemainder_Q0_independent` changes
`Q0=0` in (10.1) to every `Q0` without changing `m0`, `m`, or `N`. This is
exactly (2.6), and hence the eventual constant-relaxed statement holds with
`B_alpha=1`.

## 11. Recompilation and axiom audit commands

From the workspace root, after the mandated cache initialization, run:

```text
lake build TheoryLib
lake env lean TheoryLib/PiLongLagBlockCollisionDecay/T31T31CrossBlockAlmostEverywhere.lean
lake env lean TheoryLib/PiLongLagBlockCollisionDecay/T87T87RecordDiagonalCriticalBand.lean
lake env lean TheoryLib/PiLongLagBlockCollisionDecay/T90T90CenteredCriticalBandCore.lean
lake env lean removed-workflow-record://todo-theory-pi-long-lag-block-collision-decay-t97-1786071319-r0/theory_artifacts/T97VariablePhaseBridge.lean
```

The delivered T97 file ends with `#print axioms` for every new acceptance-facing
theorem. T31, T87, and T90 likewise end with `#print axioms` for their cited
acceptance-facing declarations. The allowed output is exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## 12. Final scope audit

| feature | retained form |
|---|---|
| problem status | variable-phase residual sibling A12 only |
| probability space | Lebesgue measure restricted to `[0,1)` |
| phase | `cos(2*pi*alpha*h*d)` only |
| scales | `1<=m`, `1<=N` |
| critical band | `10^m<=N^2<=2*10^m`, both endpoints |
| blocks | every `translatedCanonicalBlocks N` block |
| core | `0<r`, `m<=r`, `B.start<=n+r<B.finish` |
| exclusion | none survive at `(8,1)`; `Q0` retained |
| signs | both Boolean orientations, `-d,+d` |
| multipliers | every `h=1,...,10^m`, inclusive |
| width | `sqrt(B.finish^2-B.start^2)` |
| square factor | `4` |
| record diagonal | `2*10^m*sum_B K_B/w_B` |
| occurrence map | one double, two differences, two sums |
| second moment | at most `940452800*H*N^2*log(2N)` |
| full covariance | at most `117556600*H*N^2*log(2N)` |
| aggregate constant | `C0=470226400` |
| maximal tail | `940452800*10^(-m/4)` |
| eventual constant | `B_alpha=1` |
| fixed pi | no conclusion |
| C1, C2, C3 | no conclusion |
