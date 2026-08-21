# T85 source pins

Checked 2026-08-09 UTC. PDF bytes are the source pins. Text files were made
with `pdftotext -layout` and are supplied only for searchable locator checks.

## Control inputs

- `canonical_statement.txt` is the vendored byte-exact canonical statement.
  SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
- `prior-t79-REPORT.md` is the exact T79 note audited here.
  SHA-256: `7fb415a8140597f5a061b945df08eacc122e693d4998fafca98ff98aa641d800`.
  The least-valuation assertion is in Section 5, lines 181--187 of the
  delivered file. T79 is an unverified `proof sketch`, not a proved premise.

## Representation source

S. M. Abrarov and B. M. Quine, *An iteration procedure for a two-term
Machin-like formula for pi with small Lehmer's measure*, arXiv:1706.08835v3,
updated 2017-07-26.

- Versioned record: <https://arxiv.org/abs/1706.08835v3>
- Versioned PDF: <https://arxiv.org/pdf/1706.08835v3>
- PDF SHA-256: `7500ccc8cb55f651b81dd6310f02e428d2455ca6739dfb0c382435bfac8b6c3c`
- Extract SHA-256: `b5e8eff87327d624abffd4d1e45258e2ba8b5487f8b555c21b1b5fccd7e91d94`
- Exact locator: equation (3), printed/PDF p. 3, is the general two-term
  Machin-like identity; equation (5), the same page, constructs rational
  `u2`. T79's `k=4,u1=10` specialization is derived exact arithmetic, not a
  formula printed by the authors.

## Modular-sum sources

David H. Bailey and Richard E. Crandall, *Random Generators and Normal
Numbers*, Experimental Mathematics 11 (2002), 527--546; author copy dated
20 March 2003.

- DOI: <https://doi.org/10.1080/10586458.2002.10504704>
- Author PDF: <https://www.davidhbailey.com/dhbpapers/bcnormal.pdf>
- PDF SHA-256: `d6cb4c65494b8447428a480ba9c29139fcedfac47dc3fff029ec4a50a0d8db74`
- Extract SHA-256: `bab7d90671a8c5384d4251b0516c4282554062cc4bd5cdcdc9d12dc02dafec47`
- Exact locator: Lemma 4.5 and Theorem 4.6 with proof, printed pp. 12--13
  (extract lines 602--645). Theorem 4.6 fixes coprime `b,c>1`, assumes
  sufficiently large `n` and `gcd(H,c^n)<D c^n`, uses the pure-power modulus
  `c^n`, and gives the displayed square-root-modulus cost. It is a benchmark,
  not a theorem about T79's general `m_E`.

Jean Bourgain, *Mordell type exponential sum estimates in fields of prime
order*, Comptes Rendus Mathematique 339 (2004), 321--325.

- DOI: <https://doi.org/10.1016/j.crma.2004.06.013>
- Primary PDF: <https://comptes-rendus.academie-sciences.fr/mathematique/item/10.1016/j.crma.2004.06.013.pdf>
- PDF SHA-256: `4974d3596f7c86fd11d8c5d716a72481c29bc9a492cecdb6a4651c3e5db2ed23`
- Extract SHA-256: `9c06d9ad6fb3659988bfbe94d05c802132dc920303f7f72855f88854f61958b7`
- Exact locator: Theorem 3.2, printed p. 325, equation (22) (extract lines
  248--255), with order hypotheses (17)--(18) on printed p. 324 (extract
  lines 212--225). For fixed epsilon it treats prime modulus, length
  `t>p^epsilon`, and multiplicative orders exceeding `p^epsilon`.

Sergei V. Konyagin and Igor E. Shparlinski, *On the consecutive powers of a
primitive root: gaps and exponential sums*, Mathematika 58 (2012), 11--20.

- DOI: <https://doi.org/10.1112/S0025579311002117>
- Open published version: <https://research-management.mq.edu.au/ws/portalfiles/portal/62037786/Publisher%20version%20(open%20access).pdf>
- PDF SHA-256: `46f7981327913a4a7adbca724a7b3a214520ed6a946b46baba80ba8af55d97bc`
- Extract SHA-256: `ce0ac0c9ed48ac6fcd1594b5ffff62eeea83eef25cee5eba5e4c8b376fafd107`
- Exact locators: the sum `S_(g,p)(lambda,N)` is defined in equation (1)'s
  setup on printed p. 11 (extract lines 33--58). Theorem 1, printed p. 12
  (extract lines 65--76), assumes `g` is a primitive root modulo prime `p`
  and gives `p^(1/8+o(1)) N^(71/96)` for `N<=sqrt(p)` and
  `p^(23/96+o(1)) N^(49/96)` for `sqrt(p)<N<p`.

No checked source above states a theorem at length `N` comparable to `log q`
for T79's fixed base, actual numerator, and composite coprime modulus. That
frontier is derived in `REPORT.md`; it is not attributed to these papers.
