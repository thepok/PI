# T87 source and input pins

Search date: 2026-08-09 UTC. Exactly four primary sources are retained. The
search queried arXiv/DataCite, Crossref DOI records, publisher records, MathNet,
and the accepted local source inventory. A MathNet primary-PDF request for
Korobov (1972) returned HTTP 403 in this session; the retained
Bailey--Crandall paper states the needed numerator-conductor lemma and pins its
Korobov provenance. The failed retrieval is not silently treated as a source.

## Primary source 1

Yann Bugeaud and Dong Han Kim, "On the b-ary expansion of a real number whose
irrationality exponent is close to 2," arXiv:2510.02059v2, revised 2026-04-20.

- Stable identifier: `arXiv:2510.02059v2`.
- URL: https://arxiv.org/pdf/2510.02059v2
- SHA-256: `fd557275332e2a360aaf6ef55a651746fd0b271b009e1df48f5f970991723330`.
- Delivered file: `bugeaud-kim-2510.02059v2.pdf`.
- Exact locators: Theorem 1.4, PDF p. 3, equations (1.3)--(1.4); threshold
  discussion immediately below, PDF p. 3; Lemma 4.1 and restricted norm
  inequality, PDF pp. 11--12; proof of Theorem 1.4, PDF p. 12.
- Scope: Theorem 1.4 is stated for the ordinary irrationality exponent. T87's
  restricted-exponent replacement is a displayed proof-sketch localization,
  not source wording.

## Primary source 2

Yann Bugeaud and Dong Han Kim, "On the b-ary expansions of log(1+1/a) and e,"
Annali della Scuola Normale Superiore di Pisa, Classe di Scienze, 2017,
pp. 931--947.

- DOI: https://doi.org/10.2422/2036-2145.201603_002
- Publisher record: https://journals.sns.it/index.php/annaliscienze/article/view/519
- Retrieved PDF URL:
  https://journals.sns.it/index.php/annaliscienze/article/download/519/509
- SHA-256: `4a4a2d949b342c9360b78dcb8073e1fb367b910b30bba9d1be19b5f29e3f6c9d`.
- Delivered file: `bugeaud-kim-2017.pdf`.
- Exact locator: Lemma 3.6 and proof, printed pp. 944--945. The proof constructs
  a rational denominator `b^|W|*(b^|UV|-1)` and is used only in its stated
  `rep(x)<2` case.

## Primary source 3

Doron Zeilberger and Wadim Zudilin, "The irrationality measure of pi is at
most 7.103205334137...," Moscow Journal of Combinatorics and Number Theory 9
(2020), no. 4, 407--419.

- DOI: https://doi.org/10.2140/moscow.2020.9.407
- Publisher URL: https://msp.org/moscow/2020/9-4/p01.xhtml
- SHA-256: `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`.
- Delivered file: `zeilberger-zudilin-2020.pdf`.
- Exact locator: definition on printed p. 407 and final bound on printed
  p. 418. The delivered PDF is the source extract already accepted in the NRS
  source audit.

## Primary source 4

David H. Bailey and Richard E. Crandall, "Random Generators and Normal
Numbers," Experimental Mathematics 11 (2002), no. 4, 527--546.

- DOI: https://doi.org/10.1080/10586458.2002.10504704
- Author PDF: https://www.davidhbailey.com/dhbpapers/bcnormal.pdf
- SHA-256: `d6cb4c65494b8447428a480ba9c29139fcedfac47dc3fff029ec4a50a0d8db74`.
- Delivered file: `bailey-crandall-2002.pdf`.
- Exact locators: Lemma 4.5, PDF p. 13, for the `gcd(H,c)`-sensitive
  conductor bound; Theorem 4.6 and proof, PDF pp. 13--14, for comparison
  with the pure-power extension. T87 uses Lemma 4.5, not a generic
  square-root-modulus assertion.

## Accepted and review inputs

1. `canonical_statement.txt`
   - SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
   - Original project source: `knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`.
2. `PFE_T61VaalerAnalytic.lean`
   - SHA-256: `61bf75193b6581ef626fc2b061ea6ba39e4fc164ac9e49b3a0820528dc839993`.
   - Locators: strict incidence direction 2068--2077; signed premise
     2079--2094; conditional C7/C2/C1 chain 2096--2170.
3. `PFE_T86GroupedSquareBound.lean`
   - SHA-256: `29106f3d3d96a0342a50571d3cd62f1d64d4dbd13b5c9c11f514e5993d45f87b`.
   - Locators: scope 5--14; one-scale estimate 576--648; finite envelope
     784--820; `D_N<42` at 881--895; printed axiom audit follows.
4. `LL_T87RecordDiagonalCriticalBand.lean`
   - SHA-256: `88b17a0be03261d3b53fe64d09452491920ca3550194d4bd2efa22f0ca2519e4`.
   - Locators: scope 8--17; exact record count 207--251; critical normalized
     bounds 884--907; suffix ratio 909--928; printed axiom audit follows.
5. `NRS_T86_REPORT.md`
   - SHA-256: `16cff30f045a0b5bf56aa80c98c63add19d55c6a5a5b126602d8c785e48e11fa`.
   - Verification: accepted `literature-checked` audit, not a Lean theorem.
   - Locators: exact target 10--37; accepted frontiers 70--141; transfer
     budget 143--190; semantic table 570--589; negative map 591--624.
6. `T83_REVIEW_DISPOSITION.md`
   - SHA-256: `29a3cf716da0e88cd1a0b51d2c63151b945a740cf773b256dfa9f282595ad760`.
   - Verification: mixed. Listed Lean declarations are machine-checked;
     Review B remains a conjecture.
   - Locators: feedback status 35--42; literal statistic 44--175; Review A
     249--308; Review B 310--352; declaration index 354--380.
7. `SEMANTIC_OBSTRUCTION_MEMORY.md`
   - SHA-256: `aa8b0f84010f2850807e383e21f45dcb9c0dc548b5e22e0c3c4cd2779528f76f`.
   - Verification: dependency/status memory. Its proof-sketch rows are not
     premises.
   - Locators: accepted dependency table 5--18; semantic cards 35--53.
8. `WORKFLOW_CONTEXT.json`
   - SHA-256: `ec9b857c9f0703df7adaff42c410179c2fb0d56aced72cf9155cb9251ff6691d`.
   - Exact workflow input preserving the agenda, result verification levels,
     and skeptic dispositions for T83 and NRS T86.

## Retrieval blockers and exclusions

- Korobov's MathNet record is stable at
  https://doi.org/10.1070/SM1972v018n04ABEH001870, but its primary PDF returned
  HTTP 403 to the bounded retrieval command. It is not counted among the four
  retained sources.
- Kerr `arXiv:1302.4170v1` and Merai--Shparlinski `arXiv:2302.03964v1` were
  inspected during the dated search. Their prime/proper-recurrence and length
  hypotheses do not apply at the exact composite, logarithmic-length T78/T79
  frontier, so they are not retained and no theorem from them is used.
- No claim is inferred from a source merely because it appeared in search
  results or an accepted prose note.
