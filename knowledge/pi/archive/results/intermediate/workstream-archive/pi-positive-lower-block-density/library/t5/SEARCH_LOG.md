# Bounded search record

Search date: 2026-07-22 UTC. Searches are corpus-discovery records, not proof
that no other theorem exists.

## New T5 queries

| Database | Exact finite query | Retained response | Outcome |
|---|---|---|---|
| Crossref | `query.bibliographic=pi decimal normality lacunary exponential sums uniform distribution`, `rows=20`, selected fields `DOI,title,author,published,URL,type` | `searches/crossref-t5-bounded.json`, SHA-256 `b07d67d34369afaf490c40965183b92de670e318104bb17679d2443c28bdf908` | The 20 ranked records were generic exponential-sum and lacunary-series material. None stated a theorem for the fixed decimal pi orbit, so no new source was added from this query. |
| Crossref | `query.title=limit theorems lacunary series uniform distribution mod 1 law iterated logarithm discrepancies theta n x`, `rows=20`, same selected fields | `searches/crossref-t5-additional-sources.json`, SHA-256 `b484a17785aa26da995ec7b24f14dddbc56c07f4c3b2b53618db92cdfc9fdab3` | Philipp's exact DOI `10.4064/aa-26-3-241-251` is the first ranked record. The source was retained as the first additional primary source. |
| Crossref | `query.title=law of the iterated logarithm for discrepancies theta n x`, `rows=20`, same selected fields | `searches/crossref-t5-fukuyama.json`, SHA-256 `6bf24a39741a6aec1e7beac345a89075550898306a4fb073d42eb6c3b85bcaab` | Fukuyama's exact DOI `10.1007/s10474-007-6201-8` occurs in the bounded response. The source was retained as the second additional primary source. |

Exact URL:

```text
https://api.crossref.org/works?query.bibliographic=pi%20decimal%20normality%20lacunary%20exponential%20sums%20uniform%20distribution&rows=20&select=DOI,title,author,published,URL,type
```

The two exact title-search URLs are recoverable verbatim from the query rows
above by the usual percent encoding; the byte-frozen JSON responses are the
authoritative search record. `reproduce.sh verify` checks that each retained
response contains the expected DOI.

## Imported bounded discovery

The only additional primary sources in the frozen T5 corpus are Philipp 1975
and Fukuyama 2008. The retained T5 title searches above find their exact DOI
records. Accepted pi-digits T28 had independently selected the same papers
from the following three bounded searches; T5 imports T28's theorem checks
rather than rerunning them:

| T28 database/query | Bound | Retained-response SHA-256 recorded by locked T28 |
|---|---|---|
| Crossref, `query.bibliographic=lacunary exponential sums geometric progressions discrepancy` | first 20 selected records | `2f4b15f2bb581c377867228d048214419aec1ddc6dbfb642c859bcea408165cf` |
| Crossref, `query.title=law of the iterated logarithm discrepancies theta n x` | first 20 selected records | `39cd5c2a55645667404f5b974bdfd0cccf8868b065eaef7902e3202e086f8eef` |
| OpenAlex, full-text metadata search `lacunary exponential sums geometric progressions discrepancy` | first 25 records; 15 returned | `1b28f4067ab0b2e494e323eba473a1892ad6cb9348c30d185c9b8cde92d71fd1` |

The exact query definitions and hashes occur at locked T28 lines 176-194 and
in its hash manifest. The original T28 mutable response files are no longer
in the live workflow tree; they are historical cross-checks, not the retained
T5 discovery evidence. T5 does not pretend they remain available or recreate
them.

Bailey-Crandall, Lagarias, Kuipers-Niederreiter, and Weyl are required named
core sources, not additions charged against the six-source discovery cap.
Thus the corpus has two additional primary sources, below the cap of six.
