# T97 source manifest

Checked on 2026-08-06 UTC.

## Canonical statement

- File: `pi-positive-decimal-factor-entropy.txt`
- Original source URL: none; this local canonical statement was formulated by
  the system on 2026-07-22.
- SHA-256:
  `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`
- T97 scope: bounded sibling A14, not the canonical eventual question.

## Kernel-checked conventions

- T56 module:
  `TheoryLib.PiPositiveDecimalFactorEntropy.T56T56LagSectorAudit`
- Vendored inspection copy: `T56LagSectorAudit.lean`
- SHA-256:
  `41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc`
- T69 module:
  `TheoryLib.PiPositiveDecimalFactorEntropy.T69T69FiveCaseCharging`
- Vendored inspection copy: `T69FiveCaseCharging.lean`
- SHA-256:
  `43693adcb8678fd71c1ba866d91a025066b08a307a92ace165127dab1abcf3d9`
- T71 convention bridge: `T71ConventionAudit.lean`
- SHA-256:
  `228ff683b81368049f703fd1016e92131c77ce43b19406335f8a865e9e356d66`
- T71 short baseline: `T71_short_baseline.csv`
- SHA-256:
  `5349f89c3755b67d2babb83210546acfba1b7077f66c2772f95fee0d4388dd4e`

These files are hash-pinned inspection and provenance copies. T97 introduces
no Lean theorem and does not compile them as duplicate modules.

## Certified pi infrastructure

- Reused T62 program: `t62_census.py`
- SHA-256:
  `8bfe1929658644d7cb986d592d1b5afbe0b95567001c79b85d22fa3d1c5178c7`
- Author: Lorenz Milla
- Title: *A detailed proof of the Chudnovsky formula with means of basic
  complex analysis*
- Version: arXiv:1809.00533v6, 2021-03-16
- Abstract URL: `https://arxiv.org/abs/1809.00533v6`
- PDF URL: `https://arxiv.org/pdf/1809.00533v6`
- DOI: `https://doi.org/10.48550/arXiv.1809.00533`
- Pinned PDF: `milla-chudnovsky-1809.00533v6.pdf`
- PDF SHA-256:
  `69e9513d3c03c7c5c5dce12b24187b2522e0f1b08d54266a15eef93a3421cd20`
- Extracted text: `milla-chudnovsky-1809.00533v6.txt`
- Extracted-text SHA-256:
  `f1bc6daff21f730bf3e3856938f04bcf53056ee896f30f98bb7f2ebb3e7ec564`
- Exact use: Theorem 10.12, PDF p. 44, extracted-text lines 5934-5948,
  supplies the normalized Chudnovsky series identity.

The PDF has selectable text; no OCR was used. Exact alternating partial sums,
directed integer square-root bounds, and equality of directed endpoint floors
provide the decimal certificate used by the experiment.
