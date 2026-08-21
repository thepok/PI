# T173 source pins

Audit date: 2026-08-13 UTC.

Exactly one primary source was inspected. PDF bytes are authoritative. The
text derivative was produced with `pdftotext -layout` and is included only to
make exact locator checks easy.

## S1: explicit prime-counting bounds

Pierre Dusart, "Estimates of Some Functions Over Primes without R.H.,"
arXiv:1002.0442v1 (2010).

- Stable record: https://arxiv.org/abs/1002.0442v1
- Retrieval URL: https://arxiv.org/pdf/1002.0442
- Local PDF: `dusart-1002.0442v1.pdf`
- PDF SHA-256: `3f11eca84613ad00e6a447f99b318d5c3d76e360283efcc6d3eebdda25ff3923`
- Text derivative: `dusart-1002.0442v1.txt`
- Text SHA-256: `f12bc7db244353d9e69ba54d5d9d292b752eeaa11f66a9fcf576078001466f90`
- Inspected range: physical PDF pp. 1-10.
- Exact locator: physical PDF p. 9, Section 6.2, Theorem 6.9, equation
  (6.5). The text derivative has the theorem at lines 485-497. It states
  `x/log x * (1+1/log x) <= pi(x)` for `x>=599` and
  `pi(x) <= x/log x * (1+1.2762/log x)` for `x>1`.
- Use in T173: subtract the upper estimate at `10^(s-1)` from the lower
  estimate at `10^s` to obtain a lower bound for the number of `s`-digit
  primes. No normality statement is taken from this source.

## Retrieval blocker outside the source count

The historical Copeland--Erdos paper was considered only for naming context.
Its AMS PDF endpoint returned HTTP 403 to the sandbox, so it was not inspected,
is not counted as a source, and no theorem from it is used or attributed in the
report. The prime-concatenation word is instead defined directly.

```text
PRIMARY_SOURCE_COUNT: 1
PRIMARY_SOURCE_CAP: 8
RETRIEVAL_BLOCKER_COUNT: 1
```

## Vendored comparator pins (not primary sources)

`prior-comparators.tar` contains the exact named comparison artifacts used by
Section 12 of `REPORT.md`. They are local prior-work comparators, not additional
literature sources and not premises of the T173 argument. The archive members
and SHA-256 values are:

```text
1f0a50bc5286e997b897d03d49cc2613370c4cea0a20e41340f099b6278ff174  prior-T2-NormalOrbitNearReturns.lean
ad90a5a5084f7ef19f4fce052ae99330f0cab9103f2942ee164d713de2a8b5b9  prior-T89-REPORT.md
89eae292ac15699fd7175b879189d6eb5560fd692029f8a9dbdc1093583156d8  prior-T111-REPORT.md
96c685692710b05035208ca459e4536f992bef2a69c030cc318625c5de00da7a  prior-T144-REPORT.md
94858ae03b2bad5ef66a0d46fa869c3f0dd3cd62d1cf076e7ae2c7104ca30b76  prior-T160-REPORT.md
a151ea4c939c65c48d3b728664ccc26b7eb0d7c7b2826b4babf1286c060384fc  prior-T165-REPORT.md
c918090e1a3c90b7b9ea1c819e19ead8813ac8ddb830e6712a5b663d29f808ae  prior-T167-REPORT.md
c714d671805944520bce7579499c9fc6cb0201a5d6a5b3866b56c45244c44467  prior-T169-REPORT.md
74f2a8789ad54796f7c08ed52c5bc0b450e00a14bcc6867dc9db11fc52d634cf  prior-T171-REPORT.md
f7ecacfa0bd8c1e0566bd19737fb157defb8eb6fff23984718e4efe5a73e5b3f  prior-T172-REPORT.md
```
