# T132 source pins

Audit date: 2026-08-10 UTC. Exactly seven primary papers were opened. The
temporary text derivatives used for inspection are not source artifacts; the
delivered PDFs and hashes are authoritative.

## S1: Gallagher larger sieve

- P. X. Gallagher, *A larger sieve*, Acta Arithmetica 18 (1971), 77--81.
- DOI: https://doi.org/10.4064/aa-18-1-77-81
- Retrieved PDF: https://www.impan.pl/shop/publication/transaction/download/product/97714?download.pdf
- File: `gallagher-1971.pdf`
- SHA-256: `3e9adb3a74d10ab8988b6bdd35c612f3581b1e713988ba78d909b7a1dd040943`
- Exact locator: printed p. 77, Theorem 1 and formula (2); proof begins below
  formula (2) and continues on printed p. 78.
- Checked statement: if all but `g(q)` residue classes modulo every prime
  power `q` in a finite set are removed, the number of surviving integers in
  an interval of length `N` is at most
  `(sum Lambda(q)-log N)/(sum Lambda(q)/g(q)-log N)` when the denominator is
  positive.
- Scan note: image-only PDF; `pdftotext` returned no content. Theorem 1 was
  checked visually on a 300 dpi rendering. `tesseract` was unavailable, so no
  OCR text is represented as exact.

## S2: Montgomery--Vaughan large sieve

- H. L. Montgomery and R. C. Vaughan, *The large sieve*, Mathematika 20
  (1973), 119--134.
- DOI: https://doi.org/10.1112/S0025579300004708
- Retrieved PDF: https://core.ac.uk/download/286358628.pdf
- File: `montgomery-vaughan-1973.pdf`
- SHA-256: `ba1d6ec4ee264e25eb4f0ca05fede6f582c416e36566f94a5db03693b37838e5`
- Exact locator: printed p. 119, equations (1.1), (1.3), Theorem 1 and equation
  (1.4); proof in Section 2, printed pp. 122--123.
- Checked statement: for arbitrary complex coefficients on an interval of
  length `N` and frequencies of minimum circle spacing `delta`, the sum of
  squared trigonometric-polynomial values is strictly less than
  `(N+delta^(-1))*sum|a_n|^2`.

## S3: Baier--Zhao square-modulus large sieve

- Stephan Baier and Liangyi Zhao, *An Improvement for the Large Sieve for
  Square Moduli*, Journal of Number Theory 128 (2008), 154--174; inspected
  arXiv version 3 dated 2007-04-20.
- DOI: https://doi.org/10.1016/j.jnt.2007.03.004
- Retrieved PDF: https://arxiv.org/pdf/math/0512271
- File: `baier-zhao-0512271.pdf`
- SHA-256: `b0c9932adfd8ed7e48f22a84020d60f27c54def60c36f0dd2b478fbdb17280c4`
- Exact locator: preprint p. 1, equation (1.1) and definitions of `S` and `Z`;
  preprint p. 2, Theorem 1 and equation (1.7). The theorem is proved in
  Section 11.
- Checked statement: for arbitrary complex coefficients and every
  `epsilon>0`, primitive frequencies with square denominators `q^2`, `q<=Q`,
  satisfy equation (1.7) with majorant
  `(QN)^epsilon*(Q^3+N+min(N*sqrt(Q),sqrt(N)*Q^2))*Z`; the implied constant
  depends only on `epsilon`. The stated improvement range is
  `N^(1/3+epsilon)<=Q<=N^(5/12-epsilon)`.

## S4: Cicalese--Gargano--Vaccaro minimum-entropy couplings

- Ferdinando Cicalese, Luisa Gargano, and Ugo Vaccaro, *Minimum-Entropy
  Couplings and Their Applications*, IEEE Transactions on Information Theory
  65(6) (2019), 3436--3451; inspected arXiv v1.
- DOI: https://doi.org/10.1109/TIT.2019.2894519
- Retrieved PDF: https://arxiv.org/pdf/1901.07530v1
- File: `cicalese-gargano-vaccaro-1901.07530v1.pdf`
- SHA-256: `90880656635f596a65f51b329f5cdfeacf19278d4239b9db82d783ebc3c98ba3`
- Exact locator 1: PDF p. 3, Definition 1 and the majorization convention.
- Exact locator 2: PDF p. 4, Fact 1 and equation (1), coupling equations
  (3)--(5), and Lemma 2 equation (6).
- Exact locator 3: PDF p. 10, Renyi definition (20), Lemma 4 equation (21), and
  Theorem 3 equation (22). Lemma 4 covers `alpha=2`.
- Exact locator 4: PDF p. 13, Lemma 7 and its proof: a joint distribution is
  an aggregation of each of its `k` marginals and hence is majorized by their
  meet.
- Checked hypotheses: finite sorted PMFs, arbitrary coupling, and zero-padding
  for unequal lengths. No independence or asymptotic range.

## S5: Yadav--Shkel Renyi majorization lattice

- Anuj Kumar Yadav and Yanina Y. Shkel, *Geometry of Renyi Entropy on the
  Majorization Lattice*, arXiv:2605.09655v2 (2026-05-22), unpublished preprint
  as inspected.
- Abstract: https://arxiv.org/abs/2605.09655v2
- Retrieved PDF: https://arxiv.org/pdf/2605.09655v2
- File: `yadav-shkel-2605.09655v2.pdf`
- SHA-256: `3d569caf7cf50701d593a2dd57f1824f98243bdcdcfb3c98c83d6074d7007624`
- Exact locator 1: PDF p. 2, Definition 1 equation (1), Renyi entropy.
- Exact locator 2: PDF pp. 2--4, Definition 3 equation (4), Definition 7
  equation (5), Remark 3, and meet formula (7).
- Exact locator 3: PDF pp. 4--6, Theorem 1 equations (11)--(16) and Corollary 2
  equation (32).
- Exact locator 4: PDF p. 7, Theorem 3 and equation (36).
- Role: supporting confirmation of aggregation, finite meets, and all-order
  Renyi lattice statements; not a retained collision theorem.

## S6: Konieczny automatic-sequence Gowers norms

- Jakub Konieczny, *Gowers norms for the Thue--Morse and Rudin--Shapiro
  sequences*, Annales de l'Institut Fourier 69(4) (2019), 1897--1913;
  inspected arXiv v2.
- DOI: https://doi.org/10.5802/aif.3285
- Retrieved PDF: https://arxiv.org/pdf/1611.09985v2
- File: `konieczny-1611.09985v2.pdf`
- SHA-256: `92cc1e1f37a924d89bb2788d883670eba2604c2d56a029d94c750803e78c2360`
- Exact locator: preprint pp. 2--4, Definition 1.1 and Theorems A--B;
  Section 2 opening fixes `s`; preprint p. 7, Corollary 2.4 and Remark 2.5.
- Checked statement: for each fixed Gowers order there is power decay for the
  two named automatic sign sequences; no uniform growing-order constant is
  stated.

## S7: Fan--Konieczny q-multiplicative uniformity

- Aihua Fan and Jakub Konieczny, *On uniformity of q-multiplicative
  sequences*, Bulletin of the London Mathematical Society 51(2) (2019),
  264--276; inspected arXiv v2.
- DOI: https://doi.org/10.1112/blms.12245
- Retrieved PDF: https://arxiv.org/pdf/1806.04267v2
- File: `fan-konieczny-1806.04267v2.pdf`
- SHA-256: `e5fdb01f5f1c717cd5733158edcb97cf70d2f4a18f423c9ab6fd8476fb67f114`
- Exact locator: preprint pp. 1--2, q-multiplicativity, Gelfond condition (3),
  Theorems A--B and equation (5); preprint p. 9 fixes the parameters;
  preprint pp. 16--19, Proposition 5.1 and equation (65).
- Checked statement: fixed-order Gowers control for q-multiplicative sequences
  from Gelfond/Fourier input; no arbitrary weighted multiset or joint-modulus
  theorem.

## Prior evidence bundle

- File: `prior_evidence.tar.gz`
- SHA-256: `e21239cfda1d2ba118634056f38811dc24e259793b021606462d50b1e47294e0`
- Members: byte-exact T117, T118, T121, T130, and T131 reports, plus the
  explicitly unverified T124 report.
- These are comparators, not primary literature sources and not premises.
