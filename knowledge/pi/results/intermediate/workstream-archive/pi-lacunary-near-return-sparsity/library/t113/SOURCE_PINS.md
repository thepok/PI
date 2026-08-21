# T113 source pins

Audit date: 2026-08-10 UTC.

Exactly three primary sources were inspected, one in each required domain.
PDF bytes are authoritative. Text files are `pdftotext -layout` derivatives
used for line-addressable locators. No OCR was used.

## S1: restricted-denominator approximation

Nikolay G. Moshchevitin, *Density modulo 1 of sublacunary sequences:
application of Peres-Schlag's arguments*.

- Primary version: <https://arxiv.org/abs/0709.3419v2>
- PDF URL: <https://arxiv.org/pdf/0709.3419v2>
- Version/date: arXiv:0709.3419v2, 2007-10-20.
- Journal DOI: <https://doi.org/10.1007/s10958-012-0660-3>
- Delivered PDF: `moshchevitin-0709.3419v2.pdf`
- PDF SHA-256: `d6b435d06149f5b5030be9a0e31175a8b8676d64e612acee282be74fd9f874a5`
- Text derivative: `moshchevitin-0709.3419v2.txt`
- Text SHA-256: `117fc4dee8a4d5bbeef0d1d36af90599146d228f0af6529068bdd437b2ae5278`

Exact locators:

- Definition (1), printed p. 2, derivative lines 66-71: strictly increasing
  `t_n` and `H(n,tau)=min{k:t_(n+k)/t_n>=tau}`.
- Theorem 1 condition (i), printed p. 2, derivative lines 73-103: the inherited
  variable-`H` hypothesis used by Theorem 2.
- Theorem 2, printed pp. 2-3, derivative lines 107-129: monotonicity of
  `n-h(n)`, decreasing positive `delta`, conditions (i), (ii'), (iii'), and
  nonemptiness of the infinite strict-avoidance set.
- Section 6A, equations (13)-(17), printed pp. 6-7, derivative lines 424-508:
  the source's explicit direct check of the Theorem 2 hypotheses for a
  different ratio-growth model.
- Section 6B, equation (19), printed p. 8, derivative lines 538-546: the
  two-sided `exp(n^beta)` full-dimension corollary. T113 records but does not
  invoke this corollary.

Role: sole load-bearing literature theorem for T113's new direct
instantiation. The decimal-difference specialization is a new `proof sketch`,
not attributed to the source.

## S2: explicit fixed-point lacunary dynamics

Veronica Becher and Olivier Carton, *Normal numbers and nested perfect
necklaces*, Journal of Complexity 54 (2019), article 101403.

- DOI: <https://doi.org/10.1016/j.jco.2019.03.003>
- Primary version: <https://arxiv.org/abs/1805.03713v1>
- PDF URL: <https://arxiv.org/pdf/1805.03713v1>
- Version/date: arXiv:1805.03713v1, 2018-05-07.
- Delivered PDF: `becher-carton-1805.03713v1.pdf`
- PDF SHA-256: `3197ae6ff0aecb4cfc80bb89688bdc3250d09f9c11b168c9f401fdb835602448`
- Text derivative: `becher-carton-1805.03713v1.txt`
- Text SHA-256: `1350d0d9e1044d21455308fb1885db6f255f43652faad68caf53031bac40440a`

Exact locators:

- Discrepancy and base-`b` normality, preprint p. 1, derivative lines 25-48.
- Theorem 1, preprint p. 2, derivative lines 94-100: the nested-necklace
  characterization and `O((log N)^2/N)` discrepancy for the base-`b` orbit.

Role: fixed-point dynamics comparator only. T113 does not infer uniform
difference avoidance from discrepancy.

## S3: symbolic collision coding

Lior Fishman, Keith Merrill, and David Simmons, *Uniformly de Bruijn
Sequences and Symbolic Diophantine Approximation on Fractals*, Annals of
Combinatorics 22 (2018), 271-293.

- Repository URL: <https://eprints.whiterose.ac.uk/id/eprint/126995/>
- PDF URL: <https://eprints.whiterose.ac.uk/id/eprint/126995/8/10.1007_2Fs00026_018_0384_2.pdf>
- DOI: <https://doi.org/10.1007/s00026-018-0384-2>
- Version/date: published version, 2018.
- Delivered PDF: `fishman-merrill-simmons-2018.pdf`
- PDF SHA-256: `a1aa39f1783491077c55513c737895253bb7a7323fa7eb823afac672e48924d4`
- Text derivative: `fishman-merrill-simmons-2018.txt`
- Text SHA-256: `34621967d63c119b5b1f0d25fda15804cdfbb2dafaae17e0008ec9b9eaa9eff8`

Exact locators:

- Definition (2.1), printed pp. 3-4, derivative lines 137-155: non-cyclic,
  infinite, totally, and uniformly de Bruijn sequences.
- Remark 3.3, printed p. 5, derivative lines 267-279: Hamiltonian-cycle
  correction to the earlier extension argument.
- Corollary 4.3 and proof, printed pp. 10-11, derivative lines 550-617:
  positive dimension of totally de Bruijn expansions for alphabet size at
  least four and the corrected nested extension.

Role: symbolic synchronization comparator only. The T111 odd-digit
specialization and metric deductions remain an unverified prior note and are
not attributed to this source.

## Retrieval boundary

All source bytes were reused from the accepted pinned T90/T111 library; no
network retrieval was needed in this sandbox. Hashes were checked immediately
after bytewise copying. The corpus stopped at three sources because each
required domain had one exact comparator and no unresolved theorem statement
required another source.
