# T135 primary-source pins

Audit and retrieval date: 2026-08-10 UTC.

Only S1--S5 are counted as primary sources. All files are delivered locally;
the URLs record provenance and permit independent retrieval. Page numbers
below distinguish PDF pages from printed journal pages. Text extraction used
`pdftotext -layout`; every cited page produced searchable text, so OCR was not
needed.

## S1: Shannon fractional covers

- Authors: Mokshay Madiman and Prasad Tetali.
- Title: "Information Inequalities for Joint Distributions, with
  Interpretations and Applications."
- Journal: IEEE Transactions on Information Theory 56(6) (2010), 2699--2713.
- DOI: <https://doi.org/10.1109/TIT.2010.2046253>
- Version record: <https://arxiv.org/abs/0901.0044v2>
- Retrieved PDF: <https://arxiv.org/pdf/0901.0044v2>
- Local file: `madiman-tetali-0901.0044v2.pdf`
- SHA-256: `761ebe13bb09c631b65fd0b8045b9c6dfc4336ad1c1b96a607a6caae24834234`
- Exact locators:
  - PDF p. 2, Definition II: fractional covering, packing, and partition.
  - PDF p. 5, Theorem I': strong fractional Shannon-entropy form.
  - PDF p. 6, Proposition II, equation (8): weak fractional form.
- Use boundary: the entropy in the theorem is Shannon entropy. The source does
  not state a Renyi-2 fractional-cover theorem.

## S2: Renyi entropy and product additivity

- Author: Alfred Renyi.
- Title: "On Measures of Entropy and Information."
- Venue: Proceedings of the Fourth Berkeley Symposium on Mathematical
  Statistics and Probability, Volume 1 (1961), 547--561.
- Stable source page: <https://projecteuclid.org/euclid.bsmsp/1200512181>
- Retrieved PDF:
  <https://digitalassets.lib.berkeley.edu/math/ucb/text/math_s4_v1_article-27.pdf>
- Local file: `renyi-1961.pdf`
- SHA-256: `1f653d4192b783b8b87cc40cff788c17a2d04da9eb766f6614bd6f69339ea6fa`
- Exact locators:
  - PDF p. 3 / printed p. 549, equations (1.20)--(1.21): direct-product
    additivity and the order-alpha entropy formula.
  - PDF p. 7 / printed p. 553, Theorem 2 and equation (2.14): generalized
    distribution characterization.
- Use boundary: equation (1.20) is explicitly interpreted for independent
  experiments. No submodularity or dependent-coordinate Shearer claim appears
  at these locators.

## S3: Tsallis-Havrda-Charvat Shearer extension

- Author: Alexey E. Rastegin.
- Title: "Notes on Use of Generalized Entropies in Counting."
- Journal: Graphs and Combinatorics 32 (2016), 2625--2641.
- DOI: <https://doi.org/10.1007/s00373-016-1731-x>
- Version record: <https://arxiv.org/abs/1505.03256v3>
- Retrieved PDF: <https://arxiv.org/pdf/1505.03256v3>
- Local file: `rastegin-1505.03256v3.pdf`
- SHA-256: `bcbeb10f655b646d59fa61434b7c43de64f26db6c163b058a2bc9ddb70176ee0`
- Exact locators:
  - PDF p. 2, equation (2.1): Tsallis entropy definition.
  - PDF pp. 8--9, Proposition 7, equation (3.19): each coordinate belongs to
    at least `k` members and `alpha>=1` imply the THC Shearer inequality.
- Use boundary: this is Tsallis-Havrda-Charvat entropy, not Renyi entropy. At
  alpha two it gives a lower collision bound, not the desired upper bound.

## S4: dynamically driven convolution Lq dimensions

- Author: Pablo Shmerkin.
- Title: "On Furstenberg's intersection conjecture, self-similar measures, and
  the Lq norms of convolutions."
- Journal: Annals of Mathematics (2) 189(2) (2019), 319--391.
- DOI: <https://doi.org/10.4007/annals.2019.189.2.1>
- Version record: <https://arxiv.org/abs/1609.07802v3>
- Retrieved PDF: <https://arxiv.org/pdf/1609.07802v3>
- Local file: `shmerkin-1609.07802v3.pdf`
- SHA-256: `be918d5906a02c1ff17bedcc2cdb15c1c2559c6da2198bf0818b251157d824dd`
- Exact journal and local arXiv-PDF locators (the two pagination systems are
  listed independently):
  - Journal p. 329 / PDF p. 11, equations (1.3)--(1.4): convolution model and
    finite truncation.
  - Journal p. 330 / PDF p. 11, equation (1.5): recursive convolution identity.
  - Journal p. 330 / PDF p. 11, Definition 1.9: pleasant model.
  - Journal pp. 330--331 / PDF pp. 11--12, Definition 1.10: exponential
    separation.
  - Journal p. 331 / PDF p. 12, Theorem 1.11 and equation (1.6): uniform Lq
    dimension formula.
  - Journal p. 359 / PDF pp. 38--39, Theorem 5.1: finite-scale Lq
    flattening.
  - Journal p. 360 / PDF p. 39, equation (5.1) and preceding dependency list.
- Use boundary: the local factors are independent convolution factors. The
  source does not identify them with coordinate projections of one fixed word
  or with the decimal orbit of pi. The theorem gives no explicit convergence
  threshold.

## S5: incomplete geometric-progression exponential sums

- Author: Jean Bourgain.
- Title: "New bounds on exponential sums related to the Diffie--Hellman
  distributions."
- Journal: Comptes Rendus Mathematique 338(11) (2004), 825--830.
- DOI: <https://doi.org/10.1016/j.crma.2004.03.027>
- Article page:
  <https://comptes-rendus.academie-sciences.fr/mathematique/articles/10.1016/j.crma.2004.03.027/>
- Retrieved PDF:
  <https://comptes-rendus.academie-sciences.fr/mathematique/item/10.1016/j.crma.2004.03.027.pdf>
- Local file: `bourgain-2004-diffie-hellman.pdf`
- SHA-256: `d508344e2834a5d347c64d04985c293ac9eda205c3ed9f455fde86888545b7e3`
- Exact locator: PDF p. 4 / printed p. 828, Section 2.2, Theorem 2.1,
  equation (20).
- Exact sourced range: `p` prime, `theta in F_p^*` has order `t`, and
  `t>=t_1>p^delta`; the estimate is uniform in nonzero additive frequency.
- Use boundary: the positive exponent is not numerical and no first modulus is
  supplied. Equation (20) has multiplicative constant one.
  The theorem is modular and does not supply coordinate-projection
  tensorization or a fixed-pi transfer.

## Count declaration

```text
PRIMARY_SOURCE_IDS: S1,S2,S3,S4,S5
PRIMARY_SOURCE_COUNT: 5
PRIMARY_SOURCE_CAP: 10
```
