# T3: source-pinned audit of fixed-pi lacunary near returns

Audit date: 2026-07-22 UTC

Claim label: `literature-checked` for the frozen six-source corpus below. This
is not a proof that no unexamined theorem exists.

## Verdict

**Canonical C1: NOT KNOWN in the frozen corpus.** None of the six direct
primary sources in the declared corpus proves the canonical estimate for the
named starting point `x = pi`. The pair-correlation sources prove stronger
local statistics for Lebesgue-almost every multiplier, but do not identify
`pi` as a member of the full-measure set. The shrinking-target sources likewise
make almost-everywhere or Hausdorff-dimension statements, not a membership
statement for `pi`. No claim about literature outside this corpus is used.

In this audit, `NO` in an applicability cell means that the cited theorem does
not supply that component. It does not mean the canonical mathematical claim
is false. `NOT KNOWN` means the required specialization or bridge is not
established by the audited six-source corpus.

## Immutable statement and normalization

The audited statement is exactly
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`, whose SHA-256 was
recomputed as
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.

For integers `n,N >= 1`, `Q_pi(n,N)` counts ordered pairs
`(i,j) in {0,...,N-1}^2`, including `i=j`, for which

```text
||(10^i - 10^j) pi||_(R/Z) < 10^(-n).
```

The canonical quantifier string is

```text
for every integer A >= 1
  there exists an integer n0 >= 1
    such that for every integer n >= n0
      there exists an integer N >= 1
        with A*n*Q_pi(n,N) <= N^2.
```

No infinitely-many-`n`, one-fixed-`A`, every-`N`, off-diagonal-only,
almost-everywhere, normal-number, or conditional statement is substituted for
this string.

## Audit boundary and method

The corpus was frozen on 2026-07-22 before making the verdict. The finite
selection rule was: start with the direct pair and shrinking-target families
named in the canonical provenance; retain the original geometric-progression
pair theorem, its all-correlation extension, and the later
intermediate-scale paper in that citation chain; retain Philipp's direct
base-map target theorem, the modern quantitative toral extension that cites
it, and one modern moving-target self-recurrence theorem. Thus it contains:

1. The original direct pair-correlation theorem for integer geometric
   progressions.
2. Its all-local-correlations extension.
3. A later intermediate-scale pair/number-variance theorem.
4. Philipp's direct quantitative shrinking-target theorem for the base-`a`
   map.
5. A modern quantitative shrinking-target theorem for expanding toral maps.
6. A modern self-recurrence/modified-target dimension theorem that permits a
   moving target `f_n(x)=x`.

The audit is bounded to these six direct conclusions about pair counts, target
hits, or self-returns for lacunary sequences or expanding toral maps. It does
not make theorem-level claims about the Erdos-Gal, Salem-Zygmund, Philipp
discrepancy, or Fukuyama discrepancy/LIL families and does not silently treat
them as proving a pair count. This finite named-source stopping rule makes the
audit reproducible but not exhaustive.

For each included result the applicability checks are made in this fixed
order:

1. `P`: Does the theorem assert its conclusion at the named point `x = pi`?
2. `O`: Is the orbit exactly the zero-based consecutive-power window in C1,
   or is an explicit finite-shift transfer supplied?
3. `D`: Does it control the two-index circle-distance pair count, or is a
   complete transfer supplied?
4. `S`: Can its scale be made exactly `10^(-n)` without dropping large `n`?
5. `C`: Can ordered pairs and the diagonal be restored with a valid bound?
6. `Q`: Does the result support every canonical quantifier block?

The first `NO` or `NOT KNOWN` in that order is the recorded first unmatched
hypothesis. A later check is still shown to prevent an almost-everywhere
result from being misreported as fixed-pi evidence.

## Reproducible source pins

Run from this artifact directory:

```bash
sha256sum --check SOURCE_SHA256SUMS
sha256sum --check DERIVED_TEXT_SHA256SUMS
./retrieve_sources.sh /tmp/t3-pi-lacunary-source-check
```

The last command retrieves fresh copies, regenerates the text derivatives,
and checks both manifests. Full plain-text derivatives were produced with
Poppler `pdftotext -layout`, version 22.12.0, and are included under `texts/`.
PDF bytes are the authoritative source pins; the second manifest authenticates
the line-addressable derivatives used below.

| ID | Primary source and stable locator | Local PDF | SHA-256 | Exact result location |
|---|---|---|---|---|
| RZ99 | Z. Rudnick and A. Zaharescu, *A metric result on the pair correlation of fractional parts of sequences*, Acta Arith. 89 (1999), DOI [10.4064/aa-89-3-283-293](https://doi.org/10.4064/aa-89-3-283-293), [retrieval URL](https://www.impan.pl/shop/publication/transaction/download/product/110756?download.pdf) | `sources/rudnick-zaharescu-1999.pdf` | `d16de4bd2990cf6d022c9e49fff5ae59493a651db2690c74ec8aacbfc36a293f` | Definition (1.1), p. 283; Theorem 1, Proposition 2, Corollary 3, p. 284. Extract: `texts/rudnick-zaharescu-1999.txt`, lines 15-41 and 51-84. |
| RZ02 | Z. Rudnick and A. Zaharescu, *The distribution of spacings between fractional parts of lacunary sequences*, Forum Math. 14 (2002), DOI [10.1515/form.2002.030](https://doi.org/10.1515/form.2002.030), [arXiv:math/9912103v1](https://arxiv.org/abs/math/9912103v1) | `sources/rudnick-zaharescu-2002-arxiv-v1.pdf` | `4e05292f2d3541e93dd1085cb0ebbf9aded0a53358bf1410feecd0535bdb64cb` | Gap condition and Theorems 1.1-1.2, preprint pp. 1-3. Extract: `texts/rudnick-zaharescu-2002-arxiv-v1.txt`, lines 13-20 and 71-99. |
| P67 | W. Philipp, *Some metrical theorems in number theory*, Pacific J. Math. 20 (1967), DOI [10.2140/pjm.1967.20.109](https://doi.org/10.2140/pjm.1967.20.109), [journal PDF](https://msp.org/pjm/1967/20-1/pjm-v20-n1-p12-s.pdf) | `sources/philipp-1967.pdf` | `4807b5623d2341a8030f278b6d2cd4536fe6d9107fad84fa2c8894434429803f` | Base-`a` map, pp. 109-110; meaning of almost all and Theorem 2A, pp. 112-113. Extract: `texts/philipp-1967.txt`, lines 21-45, 67-72, and 154-200. |
| Y23 | N. Yesha, *Intermediate-scale statistics for real-valued lacunary sequences*, Math. Proc. Camb. Phil. Soc. 175 (2023), DOI [10.1017/S0305004123000142](https://doi.org/10.1017/S0305004123000142), [arXiv:2208.04702v1](https://arxiv.org/abs/2208.04702v1) | `sources/yesha-2023-arxiv-v1.pdf` | `3632ca5455f191d23aba79dadd74028890cc29a53b0e2cba5f4dc260c88cb275` | Definitions (1.2)-(1.3), Theorems 1.1-1.3, preprint pp. 2-4. Extract: `texts/yesha-2023-arxiv-v1.txt`, lines 80-174. |
| LLVZ23 | B. Li, L. Liao, S. Velani, E. Zorin, *The Shrinking Target Problem for Matrix Transformations of Tori: revisiting the standard problem*, Adv. Math. 421 (2023), DOI [10.1016/j.aim.2023.108994](https://doi.org/10.1016/j.aim.2023.108994), [arXiv:2208.06112v2](https://arxiv.org/abs/2208.06112v2) | `sources/li-liao-velani-zorin-2023-arxiv-v2.pdf` | `0f4c47583075a82b90a482169e382deb66729386e84621251a4e32becaa67143` | Theorem 1, preprint p. 3; Theorem 2, pp. 6-7; Corollary 2, p. 10. Extract: `texts/li-liao-velani-zorin-2023-arxiv-v2.txt`, lines 137-173, 318-353, and 475-487. |
| YW24 | N. Yuan and S. Wang, *Modified Shrinking Target Problem for Matrix Transformations of Tori*, [arXiv:2304.07532v3](https://arxiv.org/abs/2304.07532v3) | `sources/yuan-wang-2024-arxiv-v3.pdf` | `dda48b2736b62738621e9db426f8d4e99e1213020de8a77bd755d428bf04f02f` | Definitions of recurrence and modified target, pp. 2-3; Theorems 1.1-1.2 and Corollary 1.4, pp. 3-4. Extract: `texts/yuan-wang-2024-arxiv-v3.txt`, lines 37-73 and 81-173. |

## Exact theorem audit

### RZ99: direct pair correlation

Equation (1.1) defines normalized off-diagonal ordered pair correlation by

```text
(1/N) * #{1 <= j != k <= N : ||theta_j-theta_k|| <= s/N}.
```

Corollary 3 states that for each integer `g >= 2`, the fractional parts of
`alpha*g^n` have Poisson pair correlation for almost all `alpha`. More
precisely for exact zero-based alignment, Theorem 1 plus Proposition 2 permits
`a(r)=10^(r-1)` for `1 <= r <= N`. Thus the base and index set match C1, but
the conclusion still applies only to almost all multipliers.

First unmatched hypothesis: **P (NO)**. The theorem gives no criterion known
to hold for `alpha=pi` and does not assert that `pi` lies outside its unnamed
exceptional null set.

### RZ02: all local correlations

For each fixed integer lacunary sequence, Theorem 1.2 gives one full-measure
set of multipliers on which, for all `k >= 2` and all smooth compactly
supported test functions, the `k`-level correlations converge to their
Poisson limits. Taking `a(r)=10^(r-1)` and `k=2` covers the same orbit and pair
scale as RZ99 and is stronger in correlation order. To recover the sharp upper
count, fix a nonnegative smooth compactly supported majorant `f_+` of the
indicator of `[-1,1]` with integral less than `5/2`. Such a majorant follows
by smoothing the indicator of a slightly larger interval. The periodized
sharp pair count divided by `N` is at most `R_2(f_+,N)`, whose limit is the
integral of `f_+`; hence the sharp off-diagonal count is eventually at most
`3N`. Only this one fixed majorant is needed.

First unmatched hypothesis: **P (NO)**. Full Lebesgue measure is not a
membership certificate for `pi`.

### Y23: intermediate-scale pair statistic

Theorems 1.1-1.2 prove number-variance asymptotics for positive real-valued
lacunary sequences, first with high probability in the multiplier and then
for almost all multipliers in a narrower range. Equations (1.2)-(1.4) identify
this with a tent-weighted pair-correlation statistic. The paper explicitly
states that fixed `L` is allowed in Theorems 1.1-1.2 (preprint p. 4).

First unmatched hypothesis: **P (NO)**. Neither high-probability convergence
nor an almost-everywhere statement proves the statistic for `alpha=pi`.
Independently, its displayed statistic is tent-weighted rather than the sharp
indicator defining `Q_pi`, so no unconditional fixed-pi sharp-count result is
being inferred.

### P67: prescribed shrinking targets

For the base-`a` map `T(x)={a*x}`, Theorem 2A treats an arbitrary sequence of
intervals `I_n` and counts the one-index events `T^n x in I_n`, with an
asymptotic and error term for almost all starting points `x`. Setting `a=10`
matches the canonical dynamical map.

First unmatched hypothesis: **P (NO)**. The theorem does not assert its
conclusion for `x=pi mod 1`. Also, its target is prescribed independently at
each time; it does not count all two-index self-near-returns in `Q_pi`.

### LLVZ23: quantitative toral shrinking targets

Theorem 1 gives a quantitative target-hit count for summably mixing systems
for almost all points. Theorem 2 specializes it to expanding toral maps, and
Corollary 2 gives the explicit ball-count formula. In dimension one,
`T(x)=10x mod 1` is included.

First unmatched hypothesis: **P (NO)**. Every counting conclusion is
measure-almost-everywhere, not at `pi`. Moreover, the targets in the stated
counting theorem are prescribed sets and do not produce the canonical
two-index pair count.

### YW24: self-recurrence dimensions

The set `R(psi)` on preprint p. 2 and the choice `f_n(x)=x` in the modified
target set on p. 3 directly express one-index self-recurrence. Theorems
1.1-1.2 and Corollary 1.4 calculate Hausdorff dimensions of sets of points
with infinitely many such returns for expanding toral maps, including the
one-dimensional multiplier 10.

First unmatched hypothesis: **P (NO)**. A Hausdorff-dimension formula for a
limsup set does not decide whether the named point `pi mod 1` belongs to it.
It also supplies neither an upper pair-count bound nor the eventual-every-`n`
quantifier required by C1.

## Applicability matrix

Cells answer whether the cited result itself supplies the component. The
fixed decision order is `P,O,D,S,C,Q` as defined above.

| Source | P: fixed pi | O: exact base-10 orbit | D: two-index sharp pair count | S: scale `10^-n` | C: ordered + diagonal | Q: full C1 quantifiers | First unmatched |
|---|---|---|---|---|---|---|---|
| RZ99, Cor. 3 via Thm. 1 + Prop. 2 | NO | YES | YES, off-diagonal | YES, set sample size `N=10^n` | YES, add `N` | YES conditional on P | P: only almost every multiplier |
| RZ02, Thms. 1.1-1.2 | NO | YES | YES via `k=2` local pair correlation | YES, set sample size `N=10^n` | YES, add `N` | YES conditional on P | P: only a full-measure set |
| Y23, Thms. 1.1-1.2 | NO | YES | NO, theorem is tent-weighted | NOT KNOWN for the sharp count | NOT KNOWN for the sharp count | NOT KNOWN | P: high probability/almost every multiplier |
| P67, Thm. 2A | NO | NO, positive-time one-index orbit only | NO, one-index prescribed targets | YES for prescribed intervals | NO pair count to normalize | NO | P: only almost every starting point |
| LLVZ23, Thms. 1-2, Cor. 2 | NO | NO, positive-time one-index orbit only | NO, one-index prescribed targets | YES for prescribed balls | NO pair count to normalize | NO | P: only almost every starting point |
| YW24, Thms. 1.1-1.2 | NO | NO, positive-time one-index orbit only | NO, self-return limsup dimension | YES for chosen `psi` | NO upper pair count | NO, infinitely many returns only | P: dimension does not decide pi membership |

## Why fixed-point pair correlation would settle C1

This is a conditional implication used only to audit the non-`P` columns; it
is not evidence that `pi` has pair correlation.

Assume RZ99's Poisson pair-correlation conclusion at the fixed multiplier
`pi` for `a(r)=10^(r-1)`. At `s=1`, as the sample size `M` tends to infinity,

```text
#{0 <= i != j < M : ||(10^i-10^j)pi|| <= 1/M} = (2+o(1))*M.
```

For all sufficiently large `M`, this off-diagonal count is at most `3M`.
Canonical strict inequality only decreases the count. Adding the exactly `M`
diagonal pairs gives

```text
Q_pi(n,M) <= 4M whenever M=10^n is sufficiently large.
```

For each integer `A >= 1`, exponential growth gives an `n0 >= 1` such that
`4*A*n <= 10^n` for every `n >= n0`. Taking the permitted witness
`N=M=10^n` then yields

```text
A*n*Q_pi(n,N) <= 4*A*n*N <= N^2
```

for every `n >= n0`. This checks, without changing their order, all blocks
`forall A`, `exists n0`, `forall n`, and `exists N`. The only missing premise
for this route is the fixed-point statement at `pi`.

## Canonical component and quantifier verdicts

These verdicts concern what the bounded literature audit establishes about
the exact canonical statement, not what is true for generic points.

| Canonical requirement | Verdict | Reason |
|---|---|---|
| Named point `x=pi` | NOT KNOWN | Every direct asymptotic count in the corpus is metric; the dimension theorem does not decide membership. |
| Base 10 and consecutive powers `10^0,...,10^(N-1)` | YES for RZ99/RZ02; NO for an exact transfer from the target papers | RZ99/RZ02 permit `a(r)=10^(r-1)`. P67/LLVZ23/YW24 use the same map but positive-time one-index windows and already fail the pair-count check. |
| Circle distance and threshold `<10^-n` | YES conditional on fixed-pi PPC | Set pair-correlation sample size `N=10^n`; replacing `<=` by `<` can only lower the count. |
| Ordered pairs and included diagonal | YES conditional on fixed-pi PPC | RZ99 counts ordered off-diagonal pairs; exactly `N` diagonal pairs are restored. |
| `for every A >= 1` | NOT KNOWN | It follows from fixed-pi PPC by the displayed transfer, but that premise is not known for pi. |
| `there exists n0 >= 1` depending on A | NOT KNOWN | The transfer constructs it from eventual `4An <= 10^n`; fixed-pi PPC is missing. |
| `for every n >= n0` | NOT KNOWN | Full convergence would cover every sufficiently large sample size, but only for generic multipliers. No subsequence result is promoted. |
| `there exists N >= 1` depending on A,n | NOT KNOWN | The transfer would use `N=10^n`; its fixed-pi pair bound is unavailable. |
| Inequality `A*n*Q_pi(n,N) <= N^2` | NOT KNOWN | No audited theorem supplies the needed fixed-pi upper count. |
| Canonical C1 as a whole | NOT KNOWN in the frozen corpus | The first missing input on the pair-correlation route is deterministic applicability at `pi`. |

## Sibling results, not fixed-pi evidence

- RZ99 and RZ02: `YES` for almost every multiplier; **not evidence at pi**.
- Y23: `YES` for high-probability/almost-everywhere tent-weighted statistics;
  **not a sharp fixed-pi pair count**.
- P67 and LLVZ23: `YES` for almost-everywhere prescribed-target counts;
  **not a two-index fixed-pi self-near-return count**.
- YW24: `YES` for Hausdorff dimensions of self-recurrent limsup sets;
  **not membership or a counting estimate at pi**.
- Assuming fixed-pi Poisson pair correlation would settle C1, but that is a
  conditional route and is not reported as evidence.

## Retrieval and audit limitations

- `https://arxiv.org/pdf/2208.04702v2` returned HTTP 404 during retrieval;
  the explicit extant source `v1` was pinned instead.
- The IMPAN and MSP files are publisher-hosted stable URLs but not
  content-addressed. The included bytes and SHA-256 manifest are therefore
  authoritative if a publisher later regenerates a PDF.
- The audit is deliberately bounded. It supports `NOT KNOWN`, not the stronger
  universal bibliographic assertion that no theorem anywhere can apply.
- No finite computation, normality heuristic, almost-everywhere theorem, or
  conditional Fourier estimate is used as fixed-pi evidence.
