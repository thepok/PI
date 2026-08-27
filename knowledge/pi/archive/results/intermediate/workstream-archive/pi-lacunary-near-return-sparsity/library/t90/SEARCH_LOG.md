# T90 dated search log

Search date: 2026-08-09 UTC.

## Scope

The search sought theorems about a named fixed point or an explicitly
constructed orbit under an expanding multiplication map. Eligible behaviors
were shrinking targets, pair correlation, discrepancy, repunit/rational-period
resonance, or short exponential sums. Almost-everywhere results were eligible
only if they supplied an independently checkable criterion certifying the
named point.

## Queries and databases

| Database | Query or identifier | Result used |
|---|---|---|
| arXiv | `"normal numbers" "nested perfect necklaces" discrepancy` and arXiv `1805.03713` | Becher--Carton fixed low-discrepancy point |
| Crossref | DOI `10.1016/j.jco.2019.03.003` | Journal metadata for Becher--Carton |
| arXiv | `"computable absolutely normal" discrepancies` and arXiv `1511.03582` | Scheerer fixed computable point and Theorem 2.4 |
| Crossref | DOI `10.1090/mcom/3189` | Journal metadata for Scheerer |
| arXiv | `"Poissonian pair correlation" Stoneham` and arXiv `1803.05236` | Larcher--Stockinger fixed non-PPC orbit |
| Crossref | DOI `10.1016/j.disc.2019.111656` | Journal metadata for Larcher--Stockinger |
| Crossref/IMPAN | DOI `10.4064/aa-22-4-371-389` | Stoneham primary normality source and publisher PDF |
| arXiv/Crossref | arXiv `2407.13114v1`; DOI `10.1080/00029890.2025.2583887` | 2026 published status statement that `pi` is not proved normal in any base |
| accepted local library | T2, T3, T7, T10, T60, T67, T72, and `notes/t87/SEMANTIC_OBSTRUCTION_MEMORY.md` | Existing interfaces, statuses, and transfer discriminators |

The arXiv pair-correlation search also inspected recent deterministic PPC
results for sequences such as `{alpha*n^theta}`. They were not retained because
they are not fixed orbits of the multiplication-by-10 expanding map and do not
supply a transfer to `Q_pi`. Metric geometric-orbit results were already
covered by the source-pinned local T3 audit; the new search found no
fixed-point discriminator placing `pi` in their full-measure sets.

## Stopping rule

Stop after retaining at most one candidate in each of these nonduplicate
mechanism classes:

1. direct base-10 combinatorial low discrepancy;
2. direct base-10 finite exponential-sum minimization;
3. a named arithmetic expanding-map orbit separating weak near returns from
   PPC.

The resulting corpus has three candidates and five primary sources, below the
acceptance caps of three and eight. Champernowne was excluded because the
machine-checked local T2 interface already contains that solved sibling.
Additional absolutely normal constructions were excluded as mechanism
duplicates. The search is reproducible and bounded, not exhaustive.

## Search verdict

No retained source proves discrepancy decay, pair correlation, shrinking
targets, or the required adaptive exponential-sum cancellation for the fixed
point `pi`. The exact common property still absent is equidistribution of
`({10^j*pi})`, equivalently base-10 normality of `pi`.
