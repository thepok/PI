# T21 source manifest

Retrieval/audit date: 2026-07-24 UTC

All theorem statements were checked in the pinned PDFs using `pdftotext`. None of
the six PDFs is image-only. Printed and PDF page numbers are both stated whenever
they differ. Run `bash verify.sh` from this directory to verify every hash and locator.

## Canonical statement

Canonical workspace file: `knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt`

Packaged replay copy: `pi-positive-decimal-factor-entropy.txt`

SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

Origin: locally formulated canonical problem; it has no external source URL. The
workspace file was read and its hash was verified before the audit. The packaged replay
copy was made byte-for-byte from that file, preserving its lack of a terminal newline.
`bash verify.sh` checks the packaged copy by default, so the documented command works
from an isolated copy of this artifact directory. Set `CANONICAL_STATEMENT` to check a
workspace copy instead.

## F67: Furstenberg 1967

File: `sources/furstenberg-1967.pdf`

SHA-256: `cd07faa4521080272cf2c303ee4e3a41ee6a3ba9e6aea114604becaca0ba9358`

Citation: H. Furstenberg, "Disjointness in ergodic theory, minimal sets, and a
problem in Diophantine approximation," *Mathematical Systems Theory* 1 (1967),
1-49.

DOI: <https://doi.org/10.1007/BF01692494>

Retrieved PDF: <https://mathweb.ucsd.edu/~asalehig/F_Disjointness.pdf>

Retrieval note: the mirror's TLS certificate chain failed validation in the sandbox;
the bytes were retrieved with certificate checking disabled and are pinned by the
hash above. The DOI metadata independently confirms the citation.

Locator: Theorem IV.1, printed page 48, PDF page 48. Search anchors:
`T H E O R E M IV. 1.` and `irrational`.

Checked content: a nonlacunary integer semigroup sends every irrational point to a
dense subset of the circle.

## BLMV09: Bourgain-Lindenstrauss-Michel-Venkatesh 2009

File: `sources/blmv-2009.pdf`

SHA-256: `372d251b5c7c4936ab4e6b9cc6fb3af2ded2c8fe81020ad3e467843c20878e3b`

Citation: J. Bourgain, E. Lindenstrauss, P. Michel, and A. Venkatesh, "Some
effective results for times a times b," *Ergodic Theory and Dynamical Systems* 29
(2009), 1705-1722.

DOI: <https://doi.org/10.1017/S0143385708000898>

Retrieved PDF: <https://www.cambridge.org/core/services/aop-cambridge-core/content/view/01225FAD40EEBC38F3AE1A5C119D0267/S0143385708000898a.pdf/some-effective-results-for-ab.pdf>

Locators:

- Corollary 1.6, printed page 1707, PDF page 3. Search anchors:
  `C OROLLARY 1.6.` and `(log N )`.
- Theorem 1.8, printed page 1707, PDF page 3. Search anchors:
  `T HEOREM 1.8.` and `Diophantine-generic`.

Checked content: the finite rational-grid polynomial comparator and the effective
Diophantine-generic point-orbit density theorem.

## BG24: Badea-Grivaux 2024

File: `sources/badea-grivaux-2024-arxiv-v2.pdf`

SHA-256: `9e91a00704b34b4996024c907e13e1e1cc9c7caf64ede8470a5ad95239c6fe6c`

Citation: C. Badea and S. Grivaux, "Around Furstenberg's Times p, Times q
Conjecture: Times p-Invariant Measures with Some Large Fourier Coefficients,"
arXiv:2303.01089v2 (17 September 2024); subsequently *Discrete Analysis* 2024:10.

Versioned record: <https://arxiv.org/abs/2303.01089v2>

Retrieved PDF: <https://arxiv.org/pdf/2303.01089v2>

Locators:

- Conjecture 1.2, printed/PDF page 2; open-status discussion on page 3.
  Search anchors: `Conjecture 1.2.` and `Conjecture 1.2 is largely open.`
- Theorem 1.5, printed/PDF page 5. Search anchors: `Theorem 1.5` and
  `large Fourier coefficients`.

Checked content: the stronger closed-set convergence statement is identified as a
conjecture, while Theorem 1.5 concerns generic invariant measures and does not settle
the set statement.

## HS12: Hochman-Shmerkin 2012

File: `sources/hochman-shmerkin-2012.pdf`

SHA-256: `ffe34e1b8d1959fa81cf2beb3643a849f2b3c6ae0280bc15af97ea4be4f2611e`

Citation: M. Hochman and P. Shmerkin, "Local entropy averages and projections of
fractal measures," *Annals of Mathematics* 175 (2012), 1001-1059.

DOI: <https://doi.org/10.4007/annals.2012.175.3.1>

Retrieved PDF: <https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n3-p01-p.pdf>

Locator: Theorem 1.3, printed page 1005, PDF page 5. Search anchors:
`Theorem 1.3.` and `invariant under Tm , Tn`.

Checked content: expected projection dimension for products of separately invariant
measures.

## HS15: Hochman-Shmerkin 2015

File: `sources/hochman-shmerkin-2015-arxiv-v3.pdf`

SHA-256: `c8689135c75e79eb19e794be96d3062eac9ca43eb05d2c95d756175e25c11101`

Citation: M. Hochman and P. Shmerkin, "Equidistribution from fractal measures,"
arXiv:1302.5792v3 (8 December 2014), published in *Inventiones Mathematicae*
202 (2015), 427-479.

Versioned record: <https://arxiv.org/abs/1302.5792v3>

Retrieved PDF: <https://arxiv.org/pdf/1302.5792v3>

Locator: Theorem 1.10, printed/PDF page 8. Search anchors: `Theorem 1.10.` and
`positive entropy`.

Checked content: a positive-entropy invariant ergodic measure is pointwise normal in
a multiplicatively independent Pisot base.

## W19: Wu 2019

File: `sources/wu-2019.pdf`

SHA-256: `baa245bb31cc6167cc3a9d7037fe600cd0a641e7f1acac000043d3f665515314`

Citation: M. Wu, "A proof of Furstenberg's conjecture on the intersections of
times-p- and times-q-invariant sets," *Annals of Mathematics* 189 (2019),
707-751.

DOI: <https://doi.org/10.4007/annals.2019.189.3.2>

Retrieved PDF: <https://annals.math.princeton.edu/wp-content/uploads/annals-v189-n3-p02-s.pdf>

Locator: Theorem 1.4, printed page 711, PDF page 5. Search anchors:
`Theorem 1.4.` and `dimB`.

Checked content: the upper box-dimension bound for affine intersections of two
separately invariant closed sets.

## Retrieval blockers and exclusions

- The F67 mirror required bypassing a broken TLS certificate chain. The exact bytes
  are retained and hashed; the DOI is separately recorded.
- A 2023 exposition based on exponential sums was retrieved during triage but removed
  from the final package because exponential-sum ground is explicitly excluded from
  T21.
- No claims from discrepancy, BBP, irrationality-measure, or additive inverse-theorem
  literature are used in the audit.
