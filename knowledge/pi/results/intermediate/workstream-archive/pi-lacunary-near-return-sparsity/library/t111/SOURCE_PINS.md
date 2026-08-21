# T111 source pins

Audit and retrieval date: 2026-08-10 UTC.

The corpus contains exactly three primary sources, one for each required lane.
The source statements identified below are `literature-checked` against the
vendored PDFs. New specializations and deductions in `REPORT.md` are not
attributed to the sources.

## S1: synchronization and symbolic-collision coding

Lior Fishman, Keith Merrill, and David Simmons, *Uniformly de Bruijn
Sequences and Symbolic Diophantine Approximation on Fractals*, Annals of
Combinatorics 22 (2018), 271-293.

- Published-version repository URL:
  <https://eprints.whiterose.ac.uk/id/eprint/126995/8/10.1007_2Fs00026_018_0384_2.pdf>
- Repository record: <https://eprints.whiterose.ac.uk/id/eprint/126995/>
- DOI: <https://doi.org/10.1007/s00026-018-0384-2>
- Version/date: published version, 2018; source records receipt on 2016-06-25.
- Delivered PDF: `fishman-merrill-simmons-2018.pdf`.
- PDF SHA-256:
  `a1aa39f1783491077c55513c737895253bb7a7323fa7eb823afac672e48924d4`.
- `pdftotext -layout` derivative: `fishman-merrill-simmons-2018.txt`.
- Derivative SHA-256:
  `34621967d63c119b5b1f0d25fda15804cdfbb2dafaae17e0008ec9b9eaa9eff8`.

Exact locators:

- Section 2, printed pp. 3-4, definition (2.1): a non-cyclic order-`n`
  de Bruijn word has length `k^n+n-1` and contains every length-`n` word
  exactly once; `totally de Bruijn` means every positive order occurs as the
  corresponding initial prefix. Derivative lines 137-155.
- Remark 3.3, printed p. 5: the old path is not a Hamiltonian cycle, and the
  correction is to add its closing edge. Derivative lines 267-279.
- Corollary 4.3, printed p. 10, and its proof on printed pp. 10-11: for
  `k>=4`, totally de Bruijn base-`b` expansions have positive Hausdorff
  dimension; every order-`n` de Bruijn word has an order-`n+1` de Bruijn
  extension after the Hamiltonian-cycle correction. Derivative lines 550-617.

## S2: explicit marker and return-time construction

Zuzana Masakova and Edita Pelantova, *Relation between powers of factors and
recurrence function characterizing Sturmian words*.

- Primary URL/version: <https://arxiv.org/abs/0809.0603v2>.
- PDF URL: <https://arxiv.org/pdf/0809.0603v2>.
- Version/date: arXiv:0809.0603v2, 2008-09-05.
- Journal DOI: <https://doi.org/10.1016/j.tcs.2009.04.003>.
- Delivered PDF: `masakova-pelantova-0809.0603v2.pdf`.
- PDF SHA-256:
  `20087497414478431cbd704789a918b702c72687b3f8eb5e3417e1e5d98c3d43`.
- `pdftotext -layout` derivative:
  `masakova-pelantova-0809.0603v2.txt`.
- Derivative SHA-256:
  `92ea4484ae306da6859b5dee975c3497ab348e7d476a2922a7651f088472fcbc`.

Exact locators:

- Section 2, printed p. 2: Sturmian words have factor complexity
  `C(n)=n+1`. Derivative lines 82-100.
- Equation (5), printed p. 3: `R(n)+1` is the maximum complete-return length
  over length-`n` factors. Derivative lines 150-170.
- Theorem 4.1, printed p. 7: if `q_N<=n<q_(N+1)`, then
  `R(n)=q_(N+1)+q_N+n-1`. Derivative lines 376-383.

Provenance boundary: S2 explicitly attributes Theorem 4.1 to Morse and
Hedlund, *Symbolic dynamics II. Sturmian trajectories* (1940). S2 is the exact
delivered research-article locator checked here, but it is not the original
source of that formula. A direct retrieval attempt for the original JSTOR PDF
on 2026-08-10 returned HTTP 403, so no original-source pin is claimed for this
one restated theorem. The T111 rejection uses the independently displayed
Sturmian complexity obstruction; the recurrence formula is model context, not
a premise of the rejection.

## S3: restricted-denominator avoidance

Nikolay G. Moshchevitin, *Density modulo 1 of sublacunary sequences:
application of Peres-Schlag's arguments*.

- Primary URL/version: <https://arxiv.org/abs/0709.3419v2>.
- PDF URL: <https://arxiv.org/pdf/0709.3419v2>.
- Version/date: arXiv:0709.3419v2, 2007-10-20.
- Expanded journal DOI: <https://doi.org/10.1007/s10958-012-0660-3>.
- Delivered PDF: `moshchevitin-0709.3419v2.pdf`.
- PDF SHA-256:
  `d6b435d06149f5b5030be9a0e31175a8b8676d64e612acee282be74fd9f874a5`.
- `pdftotext -layout` derivative: `moshchevitin-0709.3419v2.txt`.
- Derivative SHA-256:
  `117fc4dee8a4d5bbeef0d1d36af90599146d228f0af6529068bdd437b2ae5278`.

Exact locators:

- Section 2, Theorem 1, printed pp. 2-3: finite nested closed avoidance sets
  have measure at least `eta^(K+1)` under conditions (i)-(iii). Derivative
  lines 66-105.
- Section 2, Theorem 2, printed p. 3: the infinite avoidance set is nonempty
  under conditions (i), (ii'), and (iii'). Derivative lines 107-129.
- Section 6A, equations (13)-(17), printed pp. 6-7: explicit `h(n)` and
  `delta(n)` for a ratio lower bound `t_(n+1)/t_n >= 1+gamma/n^beta`.
  Derivative lines 424-508.
- Section 6B, equation (19), printed p. 8: for
  `gamma_1 exp(n^beta)<=t_n<=gamma_2 exp(n^beta)`, `0<beta<1`, the set with
  `||t_n alpha|| > kappa/(n^(1-beta) log(n+1))` for some `kappa>0` has full
  Hausdorff dimension. Derivative lines 538-546.

## Retrieval boundary

All three retrievals succeeded. No image-only source or OCR was used. The
text derivatives are convenience locators; the pinned PDFs are authoritative.
The corpus stopped at three primary sources, below the cap of ten.
