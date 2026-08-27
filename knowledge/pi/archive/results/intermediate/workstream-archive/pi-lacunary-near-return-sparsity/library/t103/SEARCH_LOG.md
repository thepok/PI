# T103 bounded literature search log

Search date: 2026-08-09 UTC.

## Scope and stopping rule

The search sought named, explicit, positive-topological-entropy Toeplitz or
finite-rank symbolic points with quantitative pointwise tower or return-time
statements.  It stopped after finding one coordinatewise explicit candidate
whose primary construction and positive entropy could both be pinned, then
checking whether those exact sources controlled block multiplicities at tower
prefixes.  The retained corpus was capped before the agenda limits: one
candidate and two primary sources.

## Queries and routes

| Route/query | Finding |
|---|---|
| `explicit positive entropy Toeplitz sequence periodic skeleton holes` | Located the El Abdalaoui--Kasjan--Lemanczyk construction and the Downarowicz--Kasjan sequel proving its positive entropy. |
| `Toeplitz positive entropy tower return time block frequency` | General tower and filling statements were found, but no quantitative maximal-cylinder or tower-prefix collision theorem for the named point. |
| Forward references from arXiv:1304.3587 | arXiv:1502.02307 supplies the entropy proof announced but omitted in the first source. |
| `strictly ergodic positive entropy Toeplitz construction` | Parameterized constructions exist, but the inspected construction requires unspecified auxiliary choices and gives no explicit collision rate. It was not retained because it weakens the named-point criterion without repairing the quantitative gap. |
| `finite rank symbolic positive entropy` | The terminology has several incompatible meanings and the obvious finite-rank routes are associated with zero-entropy results. No candidate was needed once a strict Toeplitz point met the bounded audit. |

## Candidate decision

`z_5` was retained because:

1. every coordinate is defined recursively by explicit arithmetic
   progressions;
2. the periods are exact powers of five;
3. the stage-hole density is exactly computable;
4. positive topological entropy is proved for this construction in the sequel.

The audit found no source theorem bounding ordered block-collision
multiplicities or maximal cylinder mass along the power-of-five tower heights.
Adding more qualitative examples would not address that first missing theorem,
so the search stopped under the declared bounded rule.

## Retrieval record

```text
curl --fail --location --retry 2 --output akl-1304.3587v2.pdf \
  https://arxiv.org/pdf/1304.3587v2
pdftotext -layout akl-1304.3587v2.pdf akl-1304.3587v2.txt

curl --fail --location --retry 2 \
  --output downarowicz-kasjan-1502.02307.pdf \
  https://arxiv.org/pdf/1502.02307
pdftotext -layout downarowicz-kasjan-1502.02307.pdf \
  downarowicz-kasjan-1502.02307.txt
```

Both retrievals succeeded.  No image-only scan or OCR path was needed.
