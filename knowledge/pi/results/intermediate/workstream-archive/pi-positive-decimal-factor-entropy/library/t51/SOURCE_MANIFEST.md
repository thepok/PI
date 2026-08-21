# T51 source manifest

Access date: 2026-08-02.

## Canonical statement

- Original source URL: none recorded; the canonical question was formulated
  locally.
- Retained file: `pi-positive-decimal-factor-entropy.txt`.
- SHA-256:
  `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.
- Use: immutable canonical pi question and explicit sibling/nonclaim rules.

## Fourth-power exclusion

- Authors: Filippo Mignosi and Giuseppe Pirillo.
- Title: *Repetitions in the Fibonacci infinite word*.
- Journal: RAIRO Informatique theorique et applications 26 (1992), no. 3,
  199-204.
- DOI: <https://doi.org/10.1051/ita/1992260301991>.
- Archival record: <https://www.numdam.org/item/ITA_1992__26_3_199_0/>.
- Retrieved PDF URL:
  <https://www.numdam.org/item/ITA_1992__26_3_199_0.pdf>.
- Retained PDF: `mignosi-pirillo-1992.pdf`.
- PDF SHA-256:
  `96e3bca270ea1a52671670757e39b31be97ad1eec194d2321d241e5be253bfe1`.
- Retained approximate `pdftotext -layout` extraction:
  `mignosi-pirillo-1992.txt`.
- Text SHA-256:
  `14b77000d625a1117fced25b62453b69df07ec58adcb31d69028d85cbce90c37`.
- Exact locator: Proposition 1, printed p. 201, PDF p. 4, states that the
  Fibonacci infinite word contains no fourth power and attributes the result
  to J. Karhumaki.
- Convention cross-check: printed p. 200, PDF p. 3 defines the word by
  iterating `psi(a)=ab`, `psi(b)=a`. Under `a->0`, `b->1`, this is exactly
  `0->01`, `1->0`.

The retained PDF is the authority. Its scan-derived text is approximate and
is provided only for searching; the proposition and morphism were checked at
the displayed PDF pages.

## Kernel-checked library pins

These files are imported from the accumulated verified library rather than
duplicated. They are not mathematical premises about the T51 sibling beyond
the named generic conventions and arithmetic theorem.

| Module artifact | SHA-256 | Use |
|---|---|---|
| `t40/T40DecimalFrequencyDecimation.lean` | `9eb6b791140f6af579841ea3705b76a2decca224eb8139de456099e98bd4f5e2` | `decimalFrequency`, `decimalFrequencyAdmissible_iff`; imported by the T51 Lean range proof |
| `t10/T10ScaleAdaptiveOrbitFourier.lean` | `390946b9d5bc2f3d964b28eb98293db7c3268ad3dfe90aad2f75d4fef37fb4b8` | generic strict-band energy and ordered-pair identity |
| `t8/T8DyadicShellFejer.lean` | `dd73354bf5d978e97722f8c13eda61305c279a5bee8d7c107db04168c1f21ce1` | normalized kernel height and inverse-square decay |

The T40 pi-specific endpoint theorem is not transferred to this sibling. T51
proves its sibling endpoint identity directly from decimal shifting.

## Explicit exclusions

No conclusion from the T45 or T50 notes is cited as established. Their files
are not retained in this package. No source or theorem here concerns the
decimal expansion of pi beyond fixing the canonical open question's scope.
