# T5 source manifest

Audit date: 2026-07-24 UTC

Status: `literature-checked` for the source statements and applicability
comparisons recorded in `APPLICABILITY_MATRIX.md`. This label does not apply to
C1, which remains a `conjecture`.

## Canonical pin

- Retained canonical file: `CANONICAL_STATEMENT.txt`
- Original source URL: none; the local statement records that it was formulated
  by this system on 2026-07-23.
- SHA-256:
  `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`
- Exact locators: lines 1-10 for A1/C1; line 29 for sibling A12; lines
  38-39 for the verification rules.
- Exact target: A1/C1, ordered pairs, `|i-j| >= m`, no diagonal or overlapping
  blocks, additive `N`, and one `C_s` independent of all positive `m,N`.
- Relevant sibling: A12, the T2 long-lag residual-pair predicate. The literature
  comparison is made to A12 because the machine-checked T2 bridge maps A12 to
  C1. No source below is claimed to establish A12.

## T2 comparator pin

- Retained file: `T2UniformLongLagResidual.lean`
- SHA-256:
  `ffe231e2750445a8f2c0a342cb60e1259a2427e5bb0f8067bf1350ab62bdeba3`
- Exact locators: lines 27-37 for
  `PiUniformLongLagResidualPairDecay`; lines 39-51 for its quantifier audit;
  lines 152-166 for
  `piUniformLongLagResidualPairDecay_implies_C1` and its unchanged choice of
  `C_s` before all positive `m,N`.

The T3/T24 prose audits requested by the agenda were not present in the staged
knowledge library. The local provenance named Bailey--Crandall and the
lacunary sources Philipp, Fukuyama, Rudnick--Zaharescu, Erdos--Gal, and
Salem--Zygmund. This audit freshly pins the primary sources among those names
that state the closest usable theorems. Erdos--Gal and Salem--Zygmund occur as
antecedents inside Philipp's retained primary article; no separate theorem from
them is used in a verdict.

All formulas in quotations below are transcribed to ASCII. The retained PDF is
authoritative.

## S1: Bailey and Crandall, fixed-pi dynamical route

- Authors: David H. Bailey and Richard E. Crandall
- Title: *On the Random Character of Fundamental Constant Expansions*
- Publication: *Experimental Mathematics* 10 (2001), 175-190
- DOI: <https://doi.org/10.1080/10586458.2001.10504441>
- Retrieved author-copy URL:
  <https://www.davidhbailey.com/dhbpapers/baicran.pdf>
- Retained file: `bailey-crandall-2001-random-character.pdf`
- SHA-256:
  `8c482ef709857877ea22e4bdf9ff3fa3673dd8c20ba9f9026e3a1bded1a6704d`
- PDF properties: 25 pages, text extraction available, no OCR used.

Exact locators: PDF/article page 2, `Hypothesis A`; PDF/article page 3,
`Theorem 1.1`.

> Hypothesis A. Denote by r_n = p(n)/q(n) a rational-polynomial function,
> i.e. p,q in Z[X]. Assume further that 0 <= deg p < deg q, with r_n
> nonsingular for positive integers n. Choose an integer b >= 2 and initialize
> x_0 = 0. Then the sequence determined by
> x_n = (b x_(n-1) + r_n) mod 1
> either has a finite attractor or is equidistributed in [0,1).

> Theorem 1.1. On Hypothesis A, each of the constants pi, log 2, zeta(3) is
> normal to base 2, and log 2 is also normal to base 3.

The theorem is genuinely fixed at `pi`, but conditional on Hypothesis A and
concerns base 2 (via its underlying base-16 construction), not decimal powers. It gives no
finite-sample collision rate. Its definition of normality nevertheless does
imply a two-point statement at each fixed block length: if `A_w(N)` counts
occurrences of a binary word `w` of length `m`, then
`A_w(N)=N/2^m+o_m(N)`, hence
`sum_w A_w(N)^2=N^2/2^m+o_m(N^2)`. Removing ordered pairs at lag below `m`
changes this by only `O(mN)`. The failure is uniformity, rate, and decimal
alignment, not the complete absence of a two-point consequence.

## S2: Philipp, lacunary discrepancy

- Author: Walter Philipp
- Title: *Limit theorems for lacunary series and uniform distribution mod 1*
- Publication: *Acta Arithmetica* 26 (1975), 241-251
- DOI: <https://doi.org/10.4064/aa-26-3-241-251>
- Publisher PDF URL:
  <https://www.impan.pl/shop/publication/transaction/download/product/100600?download.pdf>
- Retained file: `philipp-1975-lacunary.pdf`
- SHA-256:
  `4d0edc8170fe1ddf368ada0fd64ed7ec48411840ab6c07fdd658e44fbae84e3a`
- PDF properties: 6 two-up scan pages; `pdftotext -layout` yielded no text.

Exact locator: PDF page 1 right half, journal page 241, definition (1.1), gap
condition (1.2), and Theorem 1/formula (1.5); continuation of the upper constant
on PDF page 2 left half, journal page 242.

Direct visual transcription from a 180-dpi rendering (no OCR engine was
available in the sandbox):

> Let <n_k, k >= 1> be a lacunary sequence of integers, i.e.
> n_(k+1)/n_k >= q > 1. Theorem 1. For almost all x,
> 32^(-1/2) <= limsup_(N->infinity)
> [N D_N(x) / sqrt(N log log N)] <= C,
> where C <= 166 + 664 (q^(1/2)-1)^(-1).

Here the source's (1.1) defines `D_N` as the supremum interval discrepancy of
the first `N` points `{n_k x}`. The rendering was inspected directly; because
the scan has no text layer and `tesseract` was unavailable, this transcription
is not an OCR claim.

At `n_k = 10^k`, the Hadamard ratio is exactly `q=10`, but the theorem still
says "almost all x". A lagwise T2 comparison requires it at every
`x_r={(10^r-1)pi}`. The displayed upper limsup constant depends only on `q`;
what may depend on `x` is the finite onset of an eventual estimate. Pullback
under multiplication by `10^r-1` and a countable intersection supply all
transformed points for almost every parameter, but do not include fixed `pi`
or make the onsets uniform in `r`.

## S3: Fukuyama, exact discrepancy LIL for geometric powers

- Author: Katusi Fukuyama
- Title: *The law of the iterated logarithm for discrepancies of {theta^n x}*
- Publication: *Acta Mathematica Hungarica* 118 (2008), 155-170
- DOI: <https://doi.org/10.1007/s10474-007-6201-8>
- Repository record: <https://hdl.handle.net/20.500.14094/90003836>
- Retained accepted-manuscript URL:
  <https://da.lib.kobe-u.ac.jp/da/kernel/90003836/90003836.pdf>
- Retained file: `fukuyama-2008-discrepancy.pdf`
- SHA-256:
  `cc825c90055c5661d4ab1923c37e320b2af7846fedc0717cb27284c52eb7a94c`
- PDF properties: 13 pages including repository cover, text extraction
  available, no OCR used.

Exact locator: PDF page 3, article page 2, unnumbered main `Theorem`.

> Theorem. For theta > 1,
> Sigma_theta := limsup_(N->infinity)
> [N D_N({theta^k x}) / sqrt(2N log log N)]
> = limsup_(N->infinity)
> [N D_N^*({theta^k x}) / sqrt(2N log log N)]
> = sup_(0<=a<1) sigma_(theta,0,a), a.e. x.

The source states the almost-everywhere qualifier on the theorem line. Taking
`theta=10` matches the decimal lacunary multiplier, but setting `x=pi` is not a
valid specialization of an almost-everywhere theorem. More precisely, a
lagwise T2 comparison requires simultaneous specialization to every
`x_r={(10^r-1)pi}`, none of which is supplied by the theorem.

## S4: Rudnick and Zaharescu, metric pair correlation

- Authors: Zeev Rudnick and Alexandru Zaharescu
- Title: *A metric result on the pair correlation of fractional parts of
  sequences*
- Publication: *Acta Arithmetica* 89 (1999), 283-293
- DOI: <https://doi.org/10.4064/aa-89-3-283-293>
- Publisher PDF URL:
  <https://www.impan.pl/shop/publication/transaction/download/product/110756?download.pdf>
- Retained file: `rudnick-zaharescu-1999-pair-correlation.pdf`
- SHA-256:
  `d16de4bd2990cf6d022c9e49fff5ae59493a651db2690c74ec8aacbfc36a293f`
- PDF properties: 11 pages, text extraction available, no OCR used.

Exact locator: PDF page 1, journal page 283, equation (1.1); PDF page 2,
journal page 284, Corollary 3.

> R_2([-s,s],N) = (1/N) #{1 <= j != k <= N :
> ||theta_j-theta_k|| <= s/N}.

> Corollary 3. Let g >= 2 be an integer. Then for almost all alpha, the
> sequence of fractional parts of alpha g^n has Poisson pair correlation.

The preceding paragraph defines Poisson pair correlation by
`R_2([-s,s],N) -> 2s` for each fixed `s`. With `g=10`, `alpha=pi`, and
`theta_j={pi 10^j}`, the pair expression is literally
`||(10^j-10^k)pi||`. The source indexes `1<=j!=k<=N`, whereas T2 uses
exponents `0,...,N-1`; replacing one endpoint point changes an ordered count
by at most `2(N-1)`, and source parameter `pi/10` gives exact zero-based
alignment. The metric theorem licenses neither fixed parameter, and the moving
scale needed by T2 is not in the corollary.

## S5: Chernov and Kleinbock, shrinking targets and cylinders

- Authors: Nikolai Chernov and Dmitry Kleinbock
- Title: *Dynamical Borel-Cantelli lemmas for Gibbs measures*
- Publication: *Israel Journal of Mathematics* 122 (2001), 1-27
- DOI: <https://doi.org/10.1007/BF02809888>
- Retained preprint: arXiv:math/9912178v1
- Retained PDF URL: <https://arxiv.org/pdf/math/9912178v1>
- Retained file: `chernov-kleinbock-1999-arxiv.pdf`
- SHA-256:
  `b779dfb61606b3991a86fe6dc3a4d1c7d1c45a81c9b746c9d799178bb00195d7`
- PDF properties: 23 pages, text extraction available, no OCR used.

Exact locator 1: PDF/article page 4, Theorem 1.7 and formula (1.1) from
Theorem 1.4 on article page 2.

> Theorem 1.7. Assume that T(x)=beta x (mod 1) with beta>1 ... and mu is
> the unique T-invariant smooth measure on [0,1]. Then any sequence {A_n} of
> subintervals (with divergent sum of measures) is an sBC sequence, and
> (1.1) holds.

> S_N = E_N + O(E_N^(1/2) log^(3/2+epsilon) E_N) for a.e. x.

Exact locator 2: PDF/article page 6, cylinder definition (2.1), Theorem 2.1,
and Examples 1-2.

> Theorem 2.1. Let {C_n} be a sequence of cylinders defined on intervals
> Lambda_n. Let D>=0 be a constant. Assume that for all m,n the intervals
> Lambda_m,Lambda_n are D-nested. Then {C_n} satisfies (SP) and hence, if in
> addition sum mu(C_n)=infinity, it is an sBC sequence and (1.1) holds.

The paper explicitly explains after Theorem 2.1 that centered cylinders are
balls and yield shrinking-target results for almost all symbolic orbits. It
does not cover a cylinder chosen from the same orbit being counted.

For Theorem 1.7 at `T(x)=10x mod 1`, the strict circle ball of radius
`rho=10^(-m)` about zero is the wrapped union
`[0,rho) union (1-rho,1)`. The theorem must therefore be invoked separately
for the two component interval sequences and the counts added. This gives main
term `2L*rho` over `L` iterates, with one `L*rho` contribution from each
component; it does not remove the almost-everywhere or lag-uniformity gaps.

## S6: Rousseau, symbolic matching

- Author: Jerome Rousseau
- Title: *Longest common substring for random subshifts of finite type*
- Publication: *Annales de l'Institut Henri Poincare, Probabilites et
  Statistiques* 57.3 (2021)
- DOI: <https://doi.org/10.1214/20-AIHP1130>
- Retained preprint: arXiv:1905.08131v2
- Retained PDF URL: <https://arxiv.org/pdf/1905.08131>
- Retained file: `rousseau-2021-longest-common-substring.pdf`
- SHA-256:
  `e9aef957042153c6f87c59b90b5c8fd72353a4f5776aaad7e0a0bf29cc1effa5`
- PDF properties: 20 pages, text extraction available, no OCR used.

Exact locator: PDF/article page 2, definition of `M_n`; PDF/article page 4,
Theorem 1.

> M_n(x,y) = max{m : x_(i+k)=y_(j+k) for k=1,...,m and for some
> 0<=i,j<=n-m}.

> Theorem 1. If 0 < lower-H_2(mu), then
> limsup_(n->infinity) M_n(x,y)/log n <= 2/lower-H_2(mu)
> for nu tensor nu-almost every pair. Moreover, if hypothesis (I-a) holds,
> then
> liminf_(n->infinity) M_n(x,y)/log n >= 2/upper-H_2(mu)
> for nu tensor nu-almost every pair.

This is a two-independent-sample extremal matching theorem. It neither counts
all matching pairs nor treats one prescribed deterministic decimal stream.

## Reproduction

From the directory containing these artifacts:

```sh
sh verify_sources.sh
pdftotext -layout rudnick-zaharescu-1999-pair-correlation.pdf rz.txt
pdftotext -layout fukuyama-2008-discrepancy.pdf fukuyama.txt
pdftotext -layout chernov-kleinbock-1999-arxiv.pdf ck.txt
pdftotext -layout rousseau-2021-longest-common-substring.pdf rousseau.txt
pdftotext -layout bailey-crandall-2001-random-character.pdf bc.txt
pdftoppm -f 1 -l 2 -png -r 180 philipp-1975-lacunary.pdf philipp
```

Search the extracted files for `Corollary 3`, `Theorem. For`, `Theorem 1.7`,
`Theorem 2.1`, `Theorem 1. If`, and `Hypothesis A`, respectively. Inspect the
two rendered Philipp pages visually at the locator above.
