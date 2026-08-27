# T90 source pins

Audit and retrieval date: 2026-08-09 UTC.

The corpus has exactly five primary sources. PDF bytes are authoritative. The
four arXiv text derivatives were made with `pdftotext -layout` from the pinned
PDFs. The Stoneham scan has no embedded text; its special handling is recorded
below.

## S1. Becher--Carton

Veronica Becher and Olivier Carton, "Normal numbers and nested perfect
necklaces," *Journal of Complexity* 54 (2019), article 101403.

- DOI: https://doi.org/10.1016/j.jco.2019.03.003
- Stable preprint: https://arxiv.org/abs/1805.03713v1
- Retrieval URL: https://arxiv.org/pdf/1805.03713v1
- Local PDF: `becher-carton-1805.03713v1.pdf`
- PDF SHA-256: `3197ae6ff0aecb4cfc80bb89688bdc3250d09f9c11b168c9f401fdb835602448`
- Text derivative: `becher-carton-1805.03713v1.txt`
- Exact locators: discrepancy definition and base-`b` normality, preprint p. 1;
  Theorem 1, p. 2.
- Line-addressable derivative: lines 25--48 and 94--100.
- Role: fixed nested-necklace construction and
  `D_N(({b^n x})_(n>=1)) = O((log N)^2/N)` for every point with the stated
  concatenation.

## S2. Scheerer

Adrian-Maria Scheerer, "Computable absolutely normal numbers and
discrepancies," *Mathematics of Computation* 86 (2017), 2911--2926.

- DOI: https://doi.org/10.1090/mcom/3189
- Stable preprint: https://arxiv.org/abs/1511.03582v2
- Retrieval URL: https://arxiv.org/pdf/1511.03582v2
- Local PDF: `scheerer-1511.03582v2.pdf`
- PDF SHA-256: `6f746011ab585043d042394e776a381a680a5ffeee6504246cdc1507570d8394`
- Text derivative: `scheerer-1511.03582v2.txt`
- Exact locators: discrepancy and normality, preprint p. 1; algorithm and
  equation (2.2), pp. 3--4; absolute normality and approximation (2.4), p. 4;
  Theorem 2.4 and equation (2.5), pp. 5--7.
- Line-addressable derivative: lines 29--40, 157--191, 227--240, and 313--326.
- Role: fixed computable point, explicit minimizing exponential-sum
  construction, and for each fixed base `r`,
  `D_N(({r^n xi})_(n>=1)) <<_r log log N/log N` for all sufficiently large
  `N`.

## S3. Stoneham

R. G. Stoneham, "On the uniform epsilon-distribution of residues within the
periods of rational fractions with applications to normal numbers,"
*Acta Arithmetica* 22 (1973), 371--389.

- DOI: https://doi.org/10.4064/aa-22-4-371-389
- Publisher page: https://www.impan.pl/get/doi/10.4064/aa-22-4-371-389
- Retrieval URL:
  https://www.impan.pl/shop/publication/transaction/download/product/98674?download.pdf
- Local PDF: `stoneham-1973.pdf`
- PDF SHA-256: `62d1718944b11b61543a20eebc2df9adbe94b94f825befa1774063897d2586d3`
- Exact locator: journal p. 372, PDF page 2, left panel, equation (1.0) and the
  sentence immediately following it.
- Role: for odd prime `p` and primitive root `g mod p^2`, the displayed
  `w(g,p)=sum_(n>=1) 1/(p^n g^(p^n))` is stated to be a transcendental
  non-Liouville normal number. The specialization `g=2,p=3` is
  `alpha_(2,3)`.

### Scan limitation

`pdftotext -layout stoneham-1973.pdf stoneham-1973.txt` produced only form-feed
characters. PDF pages 1--3 were rendered at 200 dpi with `pdftoppm` and page 2
was visually checked against the exact locator above. The environment lacked
the required `tesseract` executable, so no approximate OCR derivative is
delivered and no unverified OCR quote is presented as exact. The report uses
only equation (1.0) and its immediately following sentence, both visually
checked on the rendered page. This tooling gap is explicit rather than
silently skipped.

## S4. Larcher--Stockinger

Gerhard Larcher and Wolfgang Stockinger, "Some negative results related to
Poissonian pair correlation problems," *Discrete Mathematics* 343(2) (2020),
article 111656.

- DOI: https://doi.org/10.1016/j.disc.2019.111656
- Stable preprint: https://arxiv.org/abs/1803.05236v2
- Retrieval URL: https://arxiv.org/pdf/1803.05236v2
- Local PDF: `larcher-stockinger-1803.05236v2.pdf`
- PDF SHA-256: `a9ea7099fb191b68cd7a322bf6b50a1d009820c69c5fa16fc3d2746a1c4baeae`
- Text derivative: `larcher-stockinger-1803.05236v2.txt`
- Exact locators: PPC definition, preprint pp. 1--2; definition of
  `alpha_(2,3)` and Theorem 3, p. 4; proof of Theorem 3, pp. 14--16.
- Line-addressable derivative: lines 58--65, 162--172, and 723--840.
- Role: the fixed orbit `({2^n alpha_(2,3)})_(n in N)` is not Poissonian; the
  proof tests `s=1`, `N=2^w`, and the rational-period residue classes.

## S5. Becher--Graus

Veronica Becher and Nicole Graus, "The Discrepancy of the Champernowne
Constant," *American Mathematical Monthly* 133(2) (2026), 152--170.

- DOI: https://doi.org/10.1080/00029890.2025.2583887
- Stable preprint: https://arxiv.org/abs/2407.13114v1
- Retrieval URL: https://arxiv.org/pdf/2407.13114v1
- Local PDF: `becher-graus-2407.13114v1.pdf`
- PDF SHA-256: `675874240f96a98340683d0c0bece975efb658530956d591ce5bd0bbb4c30dd7`
- Text derivative: `becher-graus-2407.13114v1.txt`
- Text SHA-256: `8e5082e8e541bd17f2cc9254ffc5095472c737e76102c2d9fdb1c6c7f0f0fcb5`
- Exact locator: preprint p. 2, first paragraph after Figure 1.
- Line-addressable derivative: lines 63--65.
- Role: current-status statement that `pi`, `e`, and `sqrt(2)` have not been
  proved normal in any base. This source is not a retained candidate and none
  of its Champernowne estimates is used.

## Hash command

From a directory containing only the delivered artifacts:

```text
sha256sum --check SHA256SUMS
```
