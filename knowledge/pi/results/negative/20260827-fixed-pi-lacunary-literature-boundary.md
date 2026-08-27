# Fixed-pi lacunary literature boundary at the T179 correlation

Status: `literature-checked`

Date: 2026-08-27 UTC

## Search scope

The local PaperSearch database
`/home/Marcel/dev/AllMath/paper-search.sqlite3` was queried read-only after
T179 made the missing signed quantity explicit.  At audit time it contained
776,632 paper records, including 187,015 with extracted body text.  The search
target was a theorem that could control, for the actual constant pi,

\[
 \sum_{n=M}^{M+L-1} e(r a_n/10)
 H_{q,r}(x_{n+1}-c_{q,A}),
 \qquad a_n=\lfloor10x_n\rfloor,
 \quad x_n=\{10^n\pi\}.
\]

This audit found no published result in the searched material that supplies
a one-sided real-part bound for this fixed-pi, target-dependent correlation.
That is a literature boundary, not a proof that no such method exists.

## Closest source

Lagarias, [*On the Normality of Arithmetical
Constants*](https://arxiv.org/abs/math/0101055), Experimental Mathematics 10
(2001), 355--368 (PaperSearch id 5175), is the closest structural neighbor.
Its Hypothesis A would force a suitable rational BBP dynamical orbit to be
finite or uniformly distributed.  The paper leaves that hypothesis unproved
and describes it as apparently intractable.  Moreover, the known BBP system
for pi is base 16, whereas T179 is tied to the decimal predecessor map.  A
usable bridge would therefore still need either a decimal-compatible pi
forcing system or a signed base-16-to-base-10 transfer; equality of closure or
generic density is insufficient.

## Checked adjacent theories

- Aistleitner,
  [arXiv:1210.4215](https://arxiv.org/abs/1210.4215) and
  [arXiv:1306.3315](https://arxiv.org/abs/1306.3315) (PaperSearch ids 149464
  and 148346), proves quantitative metric results for lacunary/geometric
  progressions.  The exceptional set is not eliminated at `alpha = pi`.
- Fischler--Rivoal,
  [arXiv:1103.6022](https://arxiv.org/abs/1103.6022) and
  [arXiv:1512.06534](https://arxiv.org/abs/1512.06534) (ids 104823 and
  291390), supplies G-function value and integer-base rational-approximation
  machinery.  It constrains approximation or repetition, not the sign after
  the target-dependent exponential phase is applied.
- Zudilin,
  [arXiv:math/0404523](https://arxiv.org/abs/math/0404523) (id 25670), uses
  positive hypergeometric integrals for irrationality measures of pi.  The
  first missing line is decimal-denominator synchronization together with an
  oscillatory target-signed estimate.
- Adamczewski,
  [arXiv:1205.0961](https://arxiv.org/abs/1205.0961) (id 121685), gives
  integer-base expansion complexity information for exponential periods.  It
  does not control prescribed predecessor/suffix transitions.
- Broderick--Fishman--Kleinbock,
  [arXiv:1001.0318](https://arxiv.org/abs/1001.0318) (id 324407), exhibits
  full-dimensional sets of nondense lacunary orbits.  Thus Diophantine or
  fractal largeness alone cannot select pi for the required sign.
- The word "normality" in Zorin, arXiv:1309.0105, concerns Chudnovsky
  algebraic-independence normality, not radix normality.

## Exact surviving research question

The closest honest new premise is a weighted fixed-point analogue of
Lagarias's Hypothesis A: prove an explicit one-sided estimate for the T179
correlation above on suitable unbounded actual-pi blocks.  None of the
checked metric, Mahler/G-function, Pade, hypergeometric, irrationality, or
complexity results establishes that line.  Future uses of those theories must
identify the mechanism that produces the target sign, rather than citing
their unsigned or almost-everywhere conclusions.
