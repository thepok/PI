# Exact-target audit of signed Salikhov combinations

Date: 2026-10-17. Labels: **experiment** for the finite certificates and
**proof sketch** for the arguments below. No independent agent review or Lean
verification was performed in this pass. Novelty is unassessed.

## Attempt and outcome

The attempted bridge was not another approximation-rate improvement. It was
to choose **integer coefficients of either sign** in an actual Salikhov source
block so that the resulting linear form has exactly the multiplier
`10^h-16`, an integral constant term, and a small absolute error. Arbitrarily
small such errors would give the fixed-times-sixteen return in
[T69](../../../../TheoryLib/PiQuantitativeBlockHitting/T69T69FixedSixteenReturn.lean).
T69 already connects that return to V1 under its explicit joint-density premise.

This attempt did not produce the required unbounded return. An exact
rank-two lattice calculation identifies the obstruction for the tested
blocks, including all integer coefficient vectors, not merely a bounded
search. A separate measure argument shows why a fast version of this
particular numerator-congruence criterion cannot be justified by generic
normality or random-digit intuition.

This is a falsification audit, **not progress to a proved prescribed-target
transition**. The closed routes and target status are unchanged.

## Inputs and notation

Use the repository normalization

\[
I_j=a_j+b_j\pi,\quad
c_j=2^{2-\lfloor5j/2\rfloor}a_j,\quad
q_j=2^{2-\lfloor5j/2\rfloor}b_j\in\mathbb Z,
\quad\mathcal L_j=c_j+q_j\pi.
\]

The initial values and third-order recurrence are reproduced completely in
[audit.py](audit.py). They agree with the
[primary recurrence output](https://sites.math.rutgers.edu/~zeilberg/tokhniot/oSALIKHOVpi3.txt)
after multiplication of its initial values by `-5`. See also the
[repository source note at the reviewed main commit](https://github.com/thepok/PI/blob/2ab024737878cd9f1567cc296ef53f051a5ff10b/knowledge/pi/results/intermediate/20260906-salikhov-mod5-support.md).
Thirteen multipliers are additionally checked by independent integer
coefficient extraction, following the formula in
[PR18 at its reviewed head](https://github.com/thepok/PI/blob/f5794f090c9025a8bc92ff426d68f5afd220d434/workflows/experiments/salikhov_signed_block_20261017/four_source_audit.py).
No network access or external pi-digit file is needed at runtime.

For a fixed finite set of indices J, define

\[
\mathcal A_J=\{(Q,P)\in\mathbb Z^2:
 \exists(z_j)\in\mathbb Z^J,\quad
 Q=\sum_jz_jq_j,\quad P=-\sum_jz_jc_j\}.
\]

The condition P in Z is essential. For every pair in this lattice,
`Q*pi-P = sum_j z_j*L_j` exactly. The audit tries both `Q=10^h`
(the direct fully cleared tail) and `Q=10^h-16` (the T69 return).

## Exact lattice classification

Let D be a common positive denominator of all c_j, and form integer columns
`(q_j,D*c_j)`. The checker obtains their full integer span in the form

\[
\mathbb Z(g,A)+\mathbb Z(0,d),\qquad g,d>0.
\]

It constructs explicit integer source-column witnesses for both basis
vectors, verifies that every source column belongs to their span, and
independently checks `g*d` against the gcd of all two-by-two minors.
These are two-sided certificates of the span.

Put

\[
e=\gcd(D,d),\quad t=e/\gcd(A,e),\quad
G=gt,\quad M=d/e,
\]

and choose `0 <= p0 < M` satisfying

\[
(D/e)p_0\equiv-At/e\pmod M.
\]

The inverse exists because `gcd(D/e,d/e)=1`. Then

\[
\boxed{\mathcal A_J=\mathbb Z(G,p_0)+\mathbb Z(0,M).}
\]

Indeed, a specified Q first needs `g | Q`. Its possible second coordinates
are `A*(Q/g)+dZ`. Requiring one to be `-D*P` is solvable exactly when
`e | A*(Q/g)`, equivalently `G | Q`. Division by e then gives
`P = p0*(Q/G) mod M`. Conversely, that congruence supplies the needed integer
multiple of `(0,d)`. The checker also constructs source-column witnesses
for `(G,-D*p0)` and `(0,-D*M)`.

For the tested blocks, p0 is zero. Some exact outputs are:

| Source indices J | G | M | Attainable integral pairs |
|---|---:|---:|---|
| 4 through 7 | 4 | 2^10 | `Q in 4Z, P in 2^10 Z` |
| 8 through 15 | 4 | 2^18 | `Q in 4Z, P in 2^18 Z` |
| 16 through 19 | 53940 | 2^34 | `Q in 53940Z, P in 2^34 Z` |
| 16 through 23 | 620 | 2^34 | `Q in 620Z, P in 2^34 Z` |
| 16 through 31 | 4 | 2^34 | `Q in 4Z, P in 2^34 Z` |
| 16 through 79 | 4 | 2^34 | Exactly the same lattice as 16 through 31 |
| 32 through 47 | 28 | 2^66 | `Q in 28Z, P in 2^66 Z` |
| 32 through 63 | 4 | 2^66 | `Q in 4Z, P in 2^66 Z` |
| 64 through 79 | 36822656860 | 2^130 | The displayed rectangular lattice |
| 64 through 127 | 4 | 2^130 | `Q in 4Z, P in 2^130 Z` |

These are classifications for these fixed blocks, not a conjectured formula
for every dyadic block.

For J=16 through 19, J=16 through 23, and J=64 through 79, five divides G.
Therefore **no** h>=1 can give `Q=10^h-16`, regardless of coefficient sizes.
Their nonsmooth factors in G also preclude `Q=10^h` for every h>=1.
Those all-h conclusions follow from the certified fixed lattices and simple
divisibility; they do not extrapolate a finite horizon scan.

## Actual-pi target checks

The checker constructs an enclosure `(C-E)/S <= pi <= (C+E)/S` using
`pi=16*atan(1/5)-4*atan(1/239)`, alternating-series remainders, and integer
rounding bounds. Here S=2^16896 and E=62472. For each attainable Q it evaluates
its distance to the full numerator progression, with a rigorously propagated
error radius `|Q|*E/S`. There is no floating-point comparison.

For **every** integer coefficient vector on J=16 through 79 and every
`2 <= h <= 4096`, the two target systems fail even the necessary unit bound:

\[
\begin{split}
\sum z_jq_j=10^h-16,\quad P=-\sum z_jc_j\in\mathbb Z
&\Longrightarrow |(10^h-16)\pi-P|>263,\\
\sum z_jq_j=10^h,\quad P=-\sum z_jc_j\in\mathbb Z
&\Longrightarrow |10^h\pi-P|>314.
\end{split}
\]

This 64-source block contains **30 positive and 34 negative** actual linear
errors. Allowing both signs and more mixing coefficients does not remove
its integral numerator constraint.

Other finite checks and positive controls are retained:

| Source block | Minimum return error over attainable Q=10^h-16, 2<=h<=4096 |
|---|---|
| 4 through 7 | Between 0.248947789386 and 0.248947789387; h=1765 |
| 8 through 15 | Between 32.650964603520 and 32.650964603521; h=3368 |
| 16 through 31, or 16 through 79 | Between 263.893782901542 and 263.893782901543; h=2 |

The first block does have some errors below one, so the test is not designed
to reject everything. At each best attainable pair an explicit, unrestricted
integer coefficient vector is reconstructed and verified. Its recorded
L1 bit length describes that witness, not the smallest possible coefficient
norm.

Crucially, the *actual* pi orbit has a much closer finite return:

\[
0<(10^{3723}-16)\pi-P_*<0.000006924955
\]

for its nearest integer P_*, with the additional lower bound
`0.000006924954`. But `P_* = 627 mod 1024`, so this nearest integer is outside
even the smallest displayed numerator lattice. The failure of the attempted
extraction is **not** evidence that the actual orbit lacks returns. This
finite control is not new unbounded orbit information or a digit-record claim.

## A fast congruence criterion fails for almost every real number

This argument is independent of the finite samples. For an integer M>=4
that is a power of two and a positive integer Q, put

\[
E(M,Q)=\{x\in[3,4]:\operatorname{dist}(Qx,M\mathbb Z)<1\}.
\]

If `Q < M/4`, the set is empty: `Qx` lies strictly between the radius-one
neighborhoods of zero and M. Otherwise there are at most `Q/M+2` relevant
multiples of M, each contributing an interval of length at most `2/Q`.
Consequently its Lebesgue measure satisfies

\[
|E(M,Q)|\le 2/M+4/Q\le18/M.
\]

Let `M_r=2^{K(r)}`, where
`K(r)=2r+1-floor(log2(4r+1))`, r>=2, and let H(r) be any nonnegative integer
horizon bound with `sum_r H(r)/M_r < infinity`. The union bound gives

\[
\left|\left\{x\in[3,4]:\exists\,2\le h\le H(r),\ P\in M_r\mathbb Z,
 |(10^h-16)x-P|<1\right\}\right|\le18H(r)/M_r.
\]

The measure of the union over r>=R tends to zero as R tends to infinity.
Thus almost every x satisfies this condition for only finitely many r.
No independence assumption is involved. In particular the conclusion holds
for **every fixed polynomial H**, since
`1/M_r <= (4r+1)/2^(2r+1)`.

The repository's inherited companion-divisibility **proof sketch** says
`v2(c_j)>=K(j)`, and K is increasing. Therefore *any* finite integer signed
combination using only indices j>=r, if it has an integral companion P,
necessarily has `P in M_r Z`. This links the general null-set obstruction to
the proposed extraction. The finite lattice results above do not depend on
accepting that inherited all-index bound.

By the classical full-measure theorem for normal numbers (for an elementary
proof see [Weitz, 2021](https://doi.org/10.1007/s00591-021-00303-w)), there are
normal numbers failing this fast congruence criterion. Normality therefore
cannot imply the proposed criterion. **This does not prove that pi fails
it:** pi could be exceptional, and no probability claim about pi is made.
The same argument applies to `10^h` in place of `10^h-16`.

## Limits and reopening requirement

This is a restriction on **integer coefficients in the stated normalization**.
It is not a theorem against all signed linear-form methods. Different source
blocks, indices beyond those tested, horizons beyond 4096, and rational
coefficient normalizations are not ruled out.

The normalization limitation is substantial. For a displayed lattice
`4Z x MZ` with 4 dividing M, allowing source coefficients in `(1/M)Z`
permits every integral pair (Q,P): the original lattice contains `(MQ,MP)`.
So rational rescaling removes this congruence obstruction. It does not,
by itself, bound the required coefficients or control the linear-form error
without first choosing an integer close to the actual target.

Reopening the target-forcing construction requires an independent estimate
that retains the small error **after** integral-companion extraction (or
rational rescaling), with the output multiplier and numerator conditions
proved simultaneously. Selecting a nearby integer from already computed pi
digits and solving the lattice backwards supplies no such estimate.

## Reproduction

From the repository root:

```sh
python3 workflows/experiments/salikhov_target_lattice_20261017/audit.py \
  --check workflows/experiments/salikhov_target_lattice_20261017/certificate.json
```

The certificate verifies 10 actual source lattices, 800 rank-two toy lattices,
11,908 toy integral combinations, 13 independent multiplier extractions,
and 2,816 exact interval-measure cases. Both target multipliers are checked
at every shift from 2 through 4096; the minimum intervals are separated from
all competing minima. An unrestricted-numerator control is checked separately.
The infinite metric statement requires the written argument, not these tests.

No source files in TheoryLib, no axioms, and no existing knowledge or
concurrent research branches are changed. Repository-wide Lean and knowledge
checks were not run locally because a full checkout and Lean toolchain were
not available. The standalone certificate was regenerated and compared byte
for byte. Independent review is still required.
