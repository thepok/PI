# T149 primary-source pins

Audit date: 2026-08-12 UTC. Exactly four primary sources were opened, below
the cap of five. S1 and S2 are the two retained theorem candidates. S3 and S4
make the required Fourier-positivity and structured-exponential-sum screens
literal; neither is retained. PDF bytes are authoritative. Text extracts were
made by `pdftotext -layout` and are supplied only to make locators searchable.

## S1. Nonbinary three-point Terwilliger SDP (retained C-3PSD)

- Dion Gijswijt, Alexander Schrijver, and Hajime Tanaka, *New upper bounds for
  nonbinary codes based on the Terwilliger algebra and semidefinite
  programming*, Journal of Combinatorial Theory A 113 (2006), 1719-1731.
- DOI: <https://doi.org/10.1016/j.jcta.2006.03.010>
- PDF URL: <https://homepage.tudelft.nl/64a8q/papers/nonbinarycodes.pdf>
- Delivered PDF: `gijswijt-schijver-tanaka-2006.pdf`
- PDF SHA-256:
  `ff8dd592069b95aaa1e5eba07e82a667641b31405e5a7cdb4b9b308235fc4983`
- Delivered extract: `gijswijt-schijver-tanaka-2006.txt`
- Extract SHA-256:
  `f218bb3eb1b699528439435825490e32dd4e67db8131e957565f3c85ba841b4f`
- Exact locators: preprint p. 2, equations (4)-(5) and Proposition 2 define
  the ordered-triple orbit parameters (extract lines 85-129); preprint pp.
  9-10, equations (36)-(43) and Proposition 8 construct `R,R'` and their PSD
  blocks (extract lines 545-643); preprint p. 11, equation (44), Proposition
  9, equations (49)-(50) define and normalize triple counts (extract lines
  645-723).
- Checked scope: `q>=3`, `n>=1`, and an ordinary code `C subset q^n`. The
  characteristic vector is 0/1. Repetitions within an ordered triple are
  included, but multiplicities of a codeword are not part of the theorem.
  The minimum-distance zeros enter only in condition (50)(iv).

## S2. Symmetric-algebra block diagonalization (retained C-BLOCK)

- Dion Gijswijt, *Block diagonalization for algebra's associated with block
  codes*, arXiv:0910.4515v1 (2009).
- Record and DOI: <https://arxiv.org/abs/0910.4515v1>,
  <https://doi.org/10.48550/arXiv.0910.4515>
- PDF URL: <https://arxiv.org/pdf/0910.4515v1>
- Delivered PDF: `gijswijt-0910.4515v1.pdf`
- PDF SHA-256:
  `b7554d0e58abc6b32f4f1aef6bcfd689f5add8d2c56de99bd48b67ff00c71d28`
- Delivered extract: `gijswijt-0910.4515v1.txt`
- Extract SHA-256:
  `932c043893872891f8fdb9ccacbe10ef0b7732e58d87731e099a699bee8571e9`
- Exact locators: Theorem 6 and Remark 1, printed p. 7, equations (17)-(18),
  give a star-isomorphism and a PSD-preserving unnormalized block map
  (extract lines 357-391); Theorem 8, printed p. 13, equations (46)-(48),
  block diagonalizes `Sym^n(B)` (extract lines 706-733); the nonbinary Hamming
  example, printed pp. 15-16, equations (57)-(61), identifies the five-
  dimensional base algebra and its Terwilliger blocks for `q>=3` (extract
  lines 856-909).
- Checked scope: this is an algebra theorem. It preserves PSD of a matrix
  already proved PSD; it does not assert that code, multiset, overlap, or
  collision variables form such a matrix and supplies no trace upper bound.

## S3. Fourier decay from L2 flattening (screened F-L2)

- Simon Baker, Osama Khalil, and Tuomas Sahlsten, *Fourier Decay from
  L2-Flattening*, arXiv:2407.16699v3 (2024).
- Record and DOI: <https://arxiv.org/abs/2407.16699v3>,
  <https://doi.org/10.48550/arXiv.2407.16699>
- PDF URL: <https://arxiv.org/pdf/2407.16699v3>
- Delivered PDF: `baker-khalil-sahlsten-2407.16699v3.pdf`
- PDF SHA-256:
  `95f0cc2e23c1c46438b51a331dcc69922cff0c1a266d646e47e2e16c78b8b0a0`
- Delivered extract: `baker-khalil-sahlsten-2407.16699v3.txt`
- Extract SHA-256:
  `418b7a5bff7b1f2aec6bacf1ee525f0cfed66f48044a081de452e129bd0d65d1`
- Exact locators: Definition 1.1, printed p. 3, equation (1.2), gives uniform
  affine non-concentration (extract lines 113-122); Theorem 1.5, printed p. 4,
  assumes an affinely irreducible self-similar IFS with two contractions whose
  log-ratio is Diophantine and concludes polylogarithmic Fourier decay for
  every associated self-similar measure (extract lines 157-204).
- Screen: the empirical distribution of overlapping decimal blocks is not an
  invariant self-similar measure supplied by such an IFS. The theorem has no
  weighted q-ary three-point moment conclusion and no finite-depth collision
  estimate. Retaining it would duplicate a Fourier-decay lane rather than
  answer this audit.

## S4. Structured exponential sums / large sieve (screened X-LS)

- Hugh L. Montgomery and Robert C. Vaughan, *The large sieve*, Mathematika 20
  (1973), 119-134.
- DOI: <https://doi.org/10.1112/S0025579300004708>
- Retrieved PDF URL: <https://core.ac.uk/download/286358628.pdf>
- Delivered PDF: `montgomery-vaughan-1973.pdf`
- PDF SHA-256:
  `ba1d6ec4ee264e25eb4f0ca05fede6f582c416e36566f94a5db03693b37838e5`
- Delivered extract: `montgomery-vaughan-1973.txt`
- Extract SHA-256:
  `c1be79a7b3f13f6496aff93727b19bfbb2b63e1226ee5c352524e56beb631c31`
- Exact locator: printed p. 119, equations (1.1), (1.3), Theorem 1 and equation
  (1.4), extract lines 10-46. For arbitrary coefficients on an interval of
  length `N` and frequencies separated modulo one by `delta`, the sum of
  squared exponential sums is strictly below
  `(N+delta^(-1))*sum |a_n|^2`.
- Screen: decimal labels `b/10^m` have spacing only `10^(-m)`, producing the
  exponentially large `delta^(-1)=10^m` term. Repeated labels must first be
  combined into coefficients, so the theorem starts with, rather than bounds,
  their squared multiplicity. It has no three-point or overlap conclusion.

## Canonical statement

- Original URL: none. The statement's provenance says it was formulated by
  this program on 2026-07-22.
- Delivered file: `canonical_statement.txt`
- SHA-256:
  `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`
- Exact locator: line 2 is canonical A1; lines 7-23 record A1-A16.
