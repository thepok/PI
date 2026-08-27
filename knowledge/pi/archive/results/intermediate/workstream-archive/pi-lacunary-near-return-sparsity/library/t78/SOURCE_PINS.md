# T78 source pins

Checked: 2026-08-07 UTC.

## 1. Canonical statement

- Local source URL: `local:pi-lacunary-near-return-sparsity`.
- Project source: `knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`.
- Delivered byte-exact copy: `canonical_statement.txt`.
- SHA-256:
  `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
- Locator: line 2 is the ordered, diagonal-inclusive canonical question; lines
  7--23 record the excluded readings.

## 2. Euler's primary text

Leonhard Euler, *Institutiones calculi differentialis cum eius usu in analysi
finitorum ac doctrina serierum*, Pars posterior (1755), Euler Archive E212.

- Euler Archive record:
  <https://scholarlycommons.pacific.edu/euler-works/212>
- First-edition scan:
  <https://archive.org/details/bub_gb__7UPPYcsWrsC>
- Retrieved PDF:
  <https://archive.org/download/bub_gb__7UPPYcsWrsC/bub_gb__7UPPYcsWrsC.pdf>
- Delivered PDF: `euler-e212-1755.pdf`.
- PDF SHA-256:
  `c3de459c5ecf84eca7c43dcbf9b846f3c010c9b527b46d44ec0269935b405a40`.
- `pdftotext -layout` extract: `euler-e212-1755.txt`.
- Extract SHA-256:
  `2907d73d35fe0c6f18a65f28c56aee2330cdf0f4aa263bb718d3a8606ec45c68`.
- Exact locator: Pars posterior, Chapter I, section 11, Example II, printed
  p. 295, PDF page 321. The delivered page rendering
  `euler-e212-1755-p295.png` was made with
  `pdftoppm -f 321 -l 321 -png -r 150 -singlefile` and has SHA-256
  `3990269603c272b2338cf3bcdd699f574357f644a74b6052243319dccb94ab0e`.
- Visual content: Euler starts from
  `S = 1 - 1/3 + 1/5 - 1/7 + ...` and displays
  `2S = 1 + 1/3 + (1*2)/(3*5) + (1*2*3)/(3*5*7) + ...`.
  Since `S=pi/4`, this is the exact series after the elementary
  double-factorial conversion in REPORT section 1.

The scan has weak OCR. The quote and products above were checked visually
against the delivered page rendering, not inferred from its approximate OCR.

## 3. Li's exact factorial statement and beta proof

Jerome C. R. Li, proposer, "A Series for pi", Problem E854, solutions by
Ragnar Dybvik et al., *American Mathematical Monthly* 56 (1949), 633--635.

- DOI: <https://doi.org/10.2307/2304741>.
- Issue scan:
  <https://archive.org/details/sim_american-mathematical-monthly_1949-11_56_9>.
- Retrieved PDF:
  <https://archive.org/download/sim_american-mathematical-monthly_1949-11_56_9/sim_american-mathematical-monthly_1949-11_56_9.pdf>.
- Delivered PDF: `li-e854-monthly-1949.pdf`.
- PDF SHA-256:
  `cb15101243c771c5478a3d19eca8b1630fff342f7dfd0166f045e1e5a83a7603`.
- `pdftotext -layout` extract: `li-e854-monthly-1949.txt`.
- Extract SHA-256:
  `0255a930605df68e48d44980b5ac6cc17e796deac4cc0ec69b3e44cd558dad91`.
- Exact locator: printed pp. 633--635, PDF pp. 41--43. Extract lines
  2034--2052 identify E854 and give Dybvik's beta-function solution. OCR loses
  several superscripts, so the PDF is controlling.

## 4. Rabinowitz--Wagon's modern use

Stanley Rabinowitz and Stan Wagon, "A Spigot Algorithm for the Digits of pi",
*American Mathematical Monthly* 102 (1995), 195--203.

- DOI: <https://doi.org/10.1080/00029890.1995.11990560>.
- JSTOR DOI: <https://doi.org/10.2307/2975006>.
- Author-version PDF:
  <https://www.cs.williams.edu/~heeringa/classes/cs135/s15/readings/spigot.pdf>.
- Delivered PDF: `rabinowitz-wagon-spigot-1995.pdf`.
- PDF SHA-256:
  `09d968fb257e79df68e6f54e746353e346e628fdc999bfaaaa0bbf7cb114db1b`.
- `pdftotext -layout` extract: `rabinowitz-wagon-spigot-1995.txt`.
- Extract SHA-256:
  `a40a2b1a1ec27ad055619a81cab1c055791a4fdfa13343a99ee468a592f17500`.
- Exact locator: section 2, PDF p. 4, extract lines 133--151. Lines 135--140
  print the exact factorial series; lines 142--145 mention Wallis and Euler's
  transform and refer to Li.

This is a modern application and attribution trail, not the primary source.

## 5. Irrationality-measure input

Doron Zeilberger and Wadim Zudilin, "The irrationality measure of pi is at
most 7.103205334137...", *Moscow Journal of Combinatorics and Number Theory*
9 (2020), no. 4, 407--419.

- DOI: <https://doi.org/10.2140/moscow.2020.9.407>.
- Publisher page: <https://msp.org/moscow/2020/9-4/p06.xhtml>.
- Publisher PDF:
  <https://msp.org/moscow/2020/9-4/moscow-v9-n4-p06-s.pdf>.
- Delivered PDF: `zeilberger-zudilin-2020.pdf`.
- PDF SHA-256:
  `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`.
- `pdftotext -layout` extract: `zeilberger-zudilin-2020.txt`.
- Extract SHA-256:
  `49ca4907538e4ccea23cee27f051f5b33832ed2cf3e3093b4aab58a13c814a68`.
- Exact locators: printed p. 407, PDF p. 2, extract lines 27--34 define the
  irrationality measure with its eventual quantifiers. Printed p. 418, PDF
  p. 13, extract lines 676--691 concludes
  `mu(pi) <= 7.10320533413700172750577342281...`.

REPORT section 11 independently uses the rational comparisons
`mu(pi)<36/5` and `epsilon=4/5` in that definition. The resulting denominator
threshold is existential; no effective value is claimed.

## 6. Recorded square-root-modulus scale

David H. Bailey and Richard E. Crandall, "Random Generators and Normal
Numbers", *Experimental Mathematics* 11 (2002), no. 4, 527--546.

- DOI: <https://doi.org/10.1080/10586458.2002.10504704>.
- Author PDF: <https://www.davidhbailey.com/dhbpapers/bcnormal.pdf>.
- Delivered PDF: `bailey-crandall-2002.pdf`.
- PDF SHA-256:
  `d6cb4c65494b8447428a480ba9c29139fcedfac47dc3fff029ec4a50a0d8db74`.
- `pdftotext -layout` extract: `bailey-crandall-2002.txt`.
- Extract SHA-256:
  `bab7d90671a8c5384d4251b0516c4282554062cc4bd5cdcdc9d12dc02dafec47`.
- Exact locator: Theorem 4.6 and proof, printed pp. 12--13, extract lines
  621--645. For fixed coprime `b,c>1`, the theorem has a leading
  square-root-modulus cost and, source-faithfully, bounds the sum by
  `B*(A*c^(nu/2) + J*c^(-nu/2))*log(c^nu)`.

T78 does not assert that the factorial moduli meet this theorem's pure-power,
fixed-base, large-exponent, or gcd hypotheses. It proves the stronger negative
scale comparison that even the bare optimistic cost `sqrt(m_K)` exceeds the
entire available post-transient length.
