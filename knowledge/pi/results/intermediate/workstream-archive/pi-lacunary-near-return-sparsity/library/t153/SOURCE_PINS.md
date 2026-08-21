# T153 primary-source pins

Audit date: 2026-08-12 UTC.

Exactly six unique primary PDFs were opened. The source statements below are
`literature-checked` against the delivered PDFs. Deductions and applicability
comparisons in `REPORT.md` are `proof sketch`. No OCR was needed.

## S1. k-Abelian locality classes

- Domain: symbolic collision theory.
- Source: Juhani Karhumaki, Aleksi Saarela, and Luca Q. Zamboni, "On a
  generalization of Abelian equivalence and complexity of infinite words,"
  *Journal of Combinatorial Theory, Series A* 120 (2013), 2189--2206.
- arXiv: <https://arxiv.org/abs/1301.5104v1>.
- DOI: <https://doi.org/10.1016/j.jcta.2013.08.008>.
- PDF: <https://arxiv.org/pdf/1301.5104v1>.
- File: `karhumaki-saarela-zamboni-1301.5104v1.pdf`.
- SHA-256: `2b81c55bda00622055b1d86cae93b39f6f3ad83c695d2be56af24eaa0de97ef3`.
- Exact locators:
  - Definition 2.1, PDF p. 4: `k`-Abelian equivalence means equality of all
    contiguous factor counts through length `k`.
  - Lemma 2.4(1), PDF p. 5: equivalent words of equal length at most `2k-1`
    are equal. The post-Lemma 2.4 paragraph on PDF p. 6 gives distinct
    equivalent words of length `2k`, showing sharpness.
  - Lemma 2.12, PDF p. 9: a length-`k` count vector with fixed endpoints is
    realizable exactly when its weighted order-`k-1` de Bruijn graph has the
    specified Euler path, equivalently connectivity and flow balance.
  - Theorem 2.14, PDF pp. 9--10: for fixed alphabet size `q>=2` and fixed `k`,
    the number of `k`-Abelian classes in words of length `n` is
    `Theta(n^(q^k-q^(k-1)))`.
- Scope: deterministic and pointwise, but the asymptotic constants in Theorem
  2.14 are only for fixed `q,k`.

## S2. Exact cardinalities and switchings

- Domain: symbolic collision theory.
- Source: Juhani Karhumaki, Svetlana Puzynina, Michael Rao, and Markus A.
  Whiteland, "On cardinalities of k-abelian equivalence classes,"
  *Theoretical Computer Science* 658 (2017), 190--204.
- arXiv: <https://arxiv.org/abs/1605.03319v1>.
- DOI: <https://doi.org/10.1016/j.tcs.2016.06.010>.
- PDF: <https://arxiv.org/pdf/1605.03319v1>.
- File: `karhumaki-puzynina-rao-whiteland-1605.03319v1.pdf`.
- SHA-256: `3367d8b31a03e0668d194913eee528f6070b79f4a43ab29ea910a19f490f4a68`.
- Exact locators:
  - Proposition 3.3, PDF p. 5: two words are `k`-Abelian equivalent exactly
    when connected by finitely many `k`-switchings.
  - Corollary 4.3, PDF p. 6: a class consists exactly of Euler paths through
    the weighted de Bruijn graph fixed by the length-`k` census and endpoints.
  - Proposition 4.7, PDF pp. 7--8: the exact class cardinality is the displayed
    matrix-tree determinant times the product of factorial ratios.
  - Proposition 5.3, PDF p. 9: a word is a `k`-Abelian singleton exactly when
    every ordered pair of occurring length-`k-1` factors has at most one return.
- Scope: deterministic and pointwise. Singleton return-uniqueness is an extra
  global structure condition, not a consequence of a favorable short census.

## S3. Logarithmic substring reconstruction

- Domain: symbolic collision theory / metric reconstruction.
- Source: Kel Levick and Ilan Shomorony, "Fundamental Limits of Multiple
  Sequence Reconstruction from Substrings," IEEE ISIT 2023.
- arXiv: <https://arxiv.org/abs/2305.05820v1>.
- DOI: <https://doi.org/10.1109/ISIT54713.2023.10206707>.
- PDF: <https://arxiv.org/pdf/2305.05820v1>.
- File: `levick-shomorony-2305.05820v1.pdf`.
- SHA-256: `6699b77376419167ee313e74bc7304acddf0166015ab68c38d685c12c036a43a`.
- Exact locators:
  - Definition 1 and Theorem 1, PDF p. 2: for `s=n^alpha` independent uniform
    binary length-`n` strings and `k=beta log_2 n`, reconstruction from the
    union of `(k+1)`-mer sets succeeds with probability tending to one when
    `beta>max(2alpha+1,alpha+2)` and fails with probability bounded away from
    zero when `beta<max(2alpha+1,alpha+3/2)`.
  - Lemma 1, PDF p. 2: `beta>2alpha+2` makes every `k`-mer repeat-free with
    probability tending to one.
- Scope: metric over independent uniform binary sources, not a deterministic
  pointwise implication and not a theorem about multiplicity-preserving
  decimal block counts.

## S4. Regular-sequence fixed points

- Domain: fixed-point lacunary dynamics.
- Source: Michael Coons, James Evans, and Neil Manibo, "Spectral Theory of
  Regular Sequences," *Documenta Mathematica* 27 (2022), 629--653.
- DOI: <https://doi.org/10.4171/DM/880>.
- PDF: <https://content.ems.press/assets/public/full-texts/serials/dm/27/8965811/online/10.4171-dm-880.pdf>.
- File: `coons-evans-manibo-10.4171-dm-880.pdf`.
- SHA-256: `4badf20c29df7d19695675f6aa677b7e609d763c926ff99f30123bfe29fcf034`.
- Exact locators: Definition 1 and Theorem 1, printed pp. 632--633; Corollary
  2 and equation (10), printed p. 636; Theorem 5, printed pp. 643--644.
- Scope: primitive finite-dimensional regular sequences, weak limit measures,
  exact fixed-frequency matrix recursion, and a Holder limit under a joint
  spectral-radius gap. There is no growing-block occupancy theorem.
- Duplication disposition: source, theorem tuple, and NEG-M mechanism were
  already inspected in T136 and copied exactly in rejected T146.

## S5. Nonlinear fractal Fourier decay

- Domain: arithmetic or fractal Fourier decay.
- Source: Tuomas Sahlsten and Connor Stevens, "Fourier transform and expanding
  maps on Cantor sets," *American Journal of Mathematics* 146 (2024).
- arXiv: <https://arxiv.org/abs/2009.01703>.
- DOI: <https://doi.org/10.1353/ajm.2024.a932433>.
- PDF: <https://arxiv.org/pdf/2009.01703v5>.
- File: `sahlsten-stevens-2009.01703.pdf`.
- SHA-256: `ba4878034d08a46c0e5cad13b4028922ba1ae058f0a55d11f111c4d8706693bf`.
- Exact locator: total nonlinearity definition (4) and Theorem 1.1, printed
  pp. 3--4.
- Scope: polynomial Fourier decay for non-atomic Gibbs measures of totally
  nonlinear expanding Markov maps. The linear decimal map has constant
  derivative cocycle and fails total nonlinearity.
- Duplication disposition: exact source/theorem/mechanism already appears as
  T104 F3 and is screened again in T150; it cannot be a T153 candidate.

## S6. Matrix-power character sums

- Domain: short structured exponential sums.
- Source: Alina Ostafe, Igor E. Shparlinski, and Jose Felipe Voloch,
  "Equations and Character Sums with Matrix Powers, Kloosterman Sums over Small
  Subgroups, and Quantum Ergodicity," *IMRN* 2023, 14196--14238.
- arXiv: <https://arxiv.org/abs/2110.10941>.
- DOI: <https://doi.org/10.1093/imrn/rnac226>.
- PDF: <https://arxiv.org/pdf/2110.10941>.
- File: `ostafe-shparlinski-voloch-2110.10941.pdf`.
- SHA-256: `4ecd0a303f6b0c93953a2df1bd011a59e88a281745dfe363865dd6ace562c934`.
- Exact locators: equation (2.1), arXiv PDF p. 5; Theorem 2.4 and Remark 2.6,
  arXiv PDF p. 6; proof in Section 6.1.
- Scope: complete matrix orbits over finite fields, with incomplete sums only
  after completion and an extra `log q` factor. At logarithmic orbit length the
  dimension-one specialization is larger than the trivial prefix bound.
- Duplication disposition: source, theorem tuple, and NEG-X mechanism were
  already inspected in T136 and copied exactly in rejected T146.

## Retrieval record

S1--S3 were retrieved from the displayed primary arXiv PDF URLs on 2026-08-12.
S4--S6 are byte-identical copies of the prior pinned primary PDFs so the exact
duplication tests are reproducible. `pdftotext -layout` produced nonempty text
for every file. There were no retrieval failures and no OCR approximations.
