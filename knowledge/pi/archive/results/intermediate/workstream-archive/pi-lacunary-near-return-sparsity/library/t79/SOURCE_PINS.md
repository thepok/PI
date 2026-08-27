# T79 source pins

Retrieved and checked on 2026-08-07 UTC. The two PDF sources below are the
retained dated primary sources. Their `pdftotext -layout` extracts are supplied
for locator checking, but the PDF SHA-256 is the source-byte pin.

1. S. M. Abrarov and B. M. Quine, *An iteration procedure for a two-term
   Machin-like formula for pi with small Lehmer's measure*, arXiv:1706.08835v3,
   updated 2017-07-26.
   - Versioned record: <https://arxiv.org/abs/1706.08835v3>
   - Versioned PDF: <https://arxiv.org/pdf/1706.08835v3>
   - Delivered PDF: `abrarov-quine-1706.08835v3.pdf`
   - PDF SHA-256: `7500ccc8cb55f651b81dd6310f02e428d2455ca6739dfb0c382435bfac8b6c3c`
   - Extract SHA-256: `b5e8eff87327d624abffd4d1e45258e2ba8b5487f8b555c21b1b5fccd7e91d94`
   - Exact locators: equation (3), PDF p. 3, gives the two-term formula;
     equation (5), PDF p. 3, gives the rational construction of `u2`; the
     k=3 special case is displayed at PDF p. 4. This audit specializes the
     general equations itself at k=4, u1=10 using exact arithmetic.

2. David H. Bailey and Richard E. Crandall, *Random Generators and Normal
   Numbers*, Experimental Mathematics 11 (2002), 527-546; supplied source
   version dated 20 March 2003.
   - DOI: <https://doi.org/10.1080/10586458.2002.10504704>
   - Author PDF: <https://www.davidhbailey.com/dhbpapers/bcnormal.pdf>
   - Delivered PDF: `bailey-crandall-2002.pdf`
   - PDF SHA-256: `d6cb4c65494b8447428a480ba9c29139fcedfac47dc3fff029ec4a50a0d8db74`
   - Extract SHA-256: `bab7d90671a8c5384d4251b0516c4282554062cc4bd5cdcdc9d12dc02dafec47`
   - Exact locator: Theorem 4.6 and proof, printed pp. 12--13 (PDF pp. 12--13).
     It is used solely to state the square-root-modulus benchmark (5.3), not
     to claim that its hypotheses hold for the retained candidate.

The local canonical statement is a non-literature control input, supplied as
`canonical_statement.txt`, SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
