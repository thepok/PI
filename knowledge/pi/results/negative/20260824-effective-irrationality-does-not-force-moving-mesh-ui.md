# Effective irrationality does not force moving-mesh uniform integrability

Status: `proof sketch`

Date: 2026-08-24 UTC

Source: ChatGPT Pro mathematical memo in
`workflows/state/chatgpt-pro/20260824-frontier-director-d2/answer.md`, followed
by an independent definition-and-quantifier audit against the repository.

## Result

Effective irrationality, even with a substantially stronger exponent than the
published input currently used for pi, does not by itself imply either the
moving-mesh collision premise or the weaker uniform-integrability (UI)
premise.

Put

\[
 A_j=j2^j,
 \qquad
 \alpha=\sum_{j\ge1}10^{-A_j},
 \qquad
 x_n=\{10^n\alpha\}.
\]

Then:

1. `IrrationalityMeasureBelow alpha B` holds in the repository's exact
   quantifier sense for every real `B>3`, with witness `mu=3`.
2. The exact T25 predicate
   `EffectiveIrrationality alpha 4 1 (10^64)` holds.
3. The orbit has exact times-ten dynamics.
4. For every moving-mesh selection `L_j,q_j -> infinity`, the corresponding
   occupancy densities fail UI. In particular, no such selection can satisfy
   the older collision premise.

This is a generic separator, not a statement about the digits of pi. It
retires attempts to derive the active moving-mesh premise from effective
irrationality or periodic-window exclusion alone. A successful pi argument
must add genuinely pi-specific pair-correlation, numerator-sensitive, or
lag-averaged information.

## Irrationality estimate

Let

\[
 \alpha_J=\sum_{j\le J}10^{-A_j}=\frac{P_J}{10^{A_J}}.
\]

The final summand in `P_J` is one and every earlier summand is divisible by
ten, so this displayed denominator is reduced. The tail satisfies

\[
 0<R_J:=\alpha-\alpha_J
 \le \frac{10}{9}10^{-A_{J+1}}
 <\frac12 10^{-2A_J},
\]

because `A_(J+1)=2A_J+2^(J+1)`. If
`10^(A_(J-1)) <= q < 10^A_J`, then `p/q != alpha_J` and hence

\[
 \left|\alpha_J-\frac pq\right|\ge\frac1{q10^{A_J}}.
\]

Subtracting the tail gives

\[
 \left|\alpha-\frac pq\right|>
 \frac1{2q10^{A_J}}. \tag{1}
\]

For `J>=5`, `A_J/A_(J-1)<=5/2`, so (1) is greater than `q^-4` once
`q>=10^64`. More generally,

\[
 \frac{A_J}{A_{J-1}}=2+\frac2{J-1},
\]

and (1) is eventually greater than `q^(-(3+epsilon))` for every positive
`epsilon`. These are exactly the two repository predicates stated above.

## Uniform concentration

For every `n`, the terms with `A_j<=n` become integers after multiplication by
`10^n`, so

\[
 x_n=\sum_{A_j>n}10^{n-A_j}. \tag{2}
\]

For a `q`-cell mesh let `M=ceil(log_10 q)`. An index `n in [L,2L)` is
exceptional only if one of the next `M` decimal positions is some `A_j`.
Every nonexceptional index satisfies `x_n<1/q` by (2). Since `A_j>=2^j`, the
number of exceptional indices is at most

\[
 B(L,q)=M\left\lceil\log_2(2L+M)\right\rceil.
\]

Thus the first-cell occupancy obeys

\[
 n_{L,q}(0)\ge L-B(L,q). \tag{3}
\]

When `q/L` is bounded and `L,q -> infinity`, (3) gives
`n_(L,q)(0)/L -> 1`. Consequently the collision ratio satisfies

\[
 \frac{\sum_a n_{L,q}(a)^2}{L^2/q+L}
 \ge
 \frac{(1-B(L,q)/L)^2}{1/q+1/L}
 \longrightarrow\infty. \tag{4}
\]

At the explicit scales `L=A_j`, `q=L`, every point in `[L,2L)` lies in the
first cell, so the collision energy is exactly `L^2`.

## Why every UI selection fails

Consider arbitrary `L_j,q_j -> infinity`; no ratio assumption is needed.

- If `q_j/L_j` is unbounded, then for every fixed `M` there are arbitrarily
  late `j` with `q_j>M L_j`. Every occupied cell then has integer occupancy
  at least one, hence exceeds the UI threshold `M L_j/q_j`. The UI tail mass
  is exactly one.
- If `q_j/L_j` is bounded along a tail, (3) gives
  `n_j(0)/L_j -> 1`. Since `q_j -> infinity`, the first cell eventually
  exceeds every fixed UI threshold, so the UI tail mass tends to one.

Every selection has one of these behaviours after passing to a subsequence.
Therefore the UI limit cannot vanish.

## Scope corrections from audit

- In repository indexing, the long zero window begins at `a=A_j`, not
  `A_j+1`; its length is `A_(j+1)-A_j-1`. This does not change the estimate.
- The conclusion about T25 is a generic analogue of its decomposition. The
  currently formalized residual finsets are specialized to pi and prefixes.
- The repository directly supplies the arbitrary-seed fixed-frequency bridge
  only at frequency one; an all-frequency statement needs a short genericized
  conjugacy argument and is not used in the no-go above.
- No fixed-pi collision or UI premise is decided here. V1, density, and
  normality remain open.

## Lean boundary

The recommended checked slice is deliberately small: a generic theorem that
`k` consecutive zero decimal digits after orbit time `n` force

\[
 \operatorname{baseTenOrbit}(x,n)\le 10^{-k},
\]

and hence membership in the first `q`-cell whenever `q<10^k`. The full sparse
series construction, its irrationality estimate, and the UI quantifiers remain
at `proof sketch` status until separately formalized.
