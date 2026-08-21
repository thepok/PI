# T118 source pins

Search and inspection date: 2026-08-10 UTC.

`PRIMARY_SOURCE_COUNT: 4`

`RETAINED_MECHANISM_COUNT: 3`

The four PDFs below are the complete primary-source corpus opened for T118.
The PDF bytes control; text derivatives were produced earlier with
`pdftotext -layout` and are locator aids. All four were already present in the
supplied accepted knowledge library, so no mutable network retrieval was
needed. Prior reports and checked Lean modules are comparison/control inputs,
not primary literature and are not included in the count.

## S1: general-modulus completion

David H. Bailey and Richard E. Crandall, *Random Generators and Normal
Numbers*, Experimental Mathematics 11 (2002), 527-546; author copy dated
20 March 2003.

- DOI: <https://doi.org/10.1080/10586458.2002.10504704>
- Author PDF: <https://www.davidhbailey.com/dhbpapers/bcnormal.pdf>
- `bailey-crandall-2002.pdf` SHA-256:
  `d6cb4c65494b8447428a480ba9c29139fcedfac47dc3fff029ec4a50a0d8db74`.
- `bailey-crandall-2002.txt` SHA-256:
  `bab7d90671a8c5384d4251b0516c4282554062cc4bd5cdcdc9d12dc02dafec47`.
- Exact locators: Lemmas 4.3-4.5 and Theorem 4.6, author-PDF printed
  pp. 12-13; layout extract lines 570-645. Lemma 4.5 is the retained theorem.
  It fixes coprime `b,c>1`, puts `d=gcd(h,c)`, requires
  `d<c/c1(c)` and `1<=J<=ord(b,c)`, and bounds the pointwise sum by
  `sqrt(c/d)*(1+log(c/d))`. Theorem 4.6 is recorded as the pure fixed-base
  prime-power-tower comparator, not substituted for the varying T118 primes.
  For the canonical full private component, REPORT Section 6 evaluates the
  same Lemma 4.3 as `c1(P_r)=P_r`, so Lemma 4.5's gcd hypothesis is impossible.

## S2: ordered prime-prefix estimate

Bryce Kerr, *Incomplete exponential sums over exponential functions*,
Quarterly Journal of Mathematics 66 (2015), 213-224.

- Versioned record: <https://arxiv.org/abs/1302.4170v1>
- Versioned PDF: <https://arxiv.org/pdf/1302.4170v1>
- DOI: <https://doi.org/10.1093/qmath/hau015>
- `kerr-1302.4170v1.pdf` SHA-256:
  `9136dc3965da376942f653b2b06de8d92d7e5e997ee536e1257979698b73e4bd`.
- `kerr-1302.4170v1.txt` SHA-256:
  `2a13bcbb1416ceaf783095661282cf08f9834a71b7a71a97f750d7c314d6ea6b`.
- Exact locators: definition (1), printed p. 1; Theorems 1-3, printed
  pp. 2-3; layout extract lines 69-101. Theorem 2 is retained. For prime `p`,
  `g` of order `t`, and `N<=t`, its first branch `N<=sqrt(t)` is
  `p^(1/8) N^(71/96+o(1))`, uniformly over nonzero numerators. The other two
  branches are displayed in the same theorem.

## S3: prime-field sum-product estimate

Jean Bourgain, *Mordell type exponential sum estimates in fields of prime
order*, Comptes Rendus Mathematique 339 (2004), 321-325.

- DOI: <https://doi.org/10.1016/j.crma.2004.06.013>
- Publisher PDF:
  <https://comptes-rendus.academie-sciences.fr/mathematique/item/10.1016/j.crma.2004.06.013.pdf>
- `bourgain-2004.pdf` SHA-256:
  `4974d3596f7c86fd11d8c5d716a72481c29bc9a492cecdb6a4651c3e5db2ed23`.
- `bourgain-2004.txt` SHA-256:
  `9c06d9ad6fb3659988bfbe94d05c802132dc920303f7f72855f88854f61958b7`.
- Exact locators: order hypotheses (17)-(18), printed p. 324; Theorem 3.2
  and equation (22), printed p. 325; layout extract lines 210-255. For fixed
  `epsilon>0`, it requires every relevant order and the length `t` to exceed
  `p^epsilon`, then gives a pointwise `p^(-delta)t` bound. The one-base ratio
  condition is vacuous.

## S4: irrationality exponent

Doron Zeilberger and Wadim Zudilin, *The irrationality measure of pi is at
most 7.103205334137...*, Moscow Journal of Combinatorics and Number Theory 9
(2020), 407-419.

- DOI: <https://doi.org/10.2140/moscow.2020.9.407>
- Publisher PDF: <https://msp.org/moscow/2020/9-4/moscow-v9-n4-p06-s.pdf>
- `zeilberger-zudilin-2020.pdf` SHA-256:
  `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`.
- `zeilberger-zudilin-2020.txt` SHA-256:
  `49ca4907538e4ccea23cee27f051f5b33832ed2cf3e3093b4aab58a13c814a68`.
- Exact locators: the definition with eventual quantifiers is printed p. 407,
  PDF p. 2, extract lines 27-34. The final bound
  `mu(pi)<=7.1032053341370017275...` is printed p. 418, PDF p. 13, extract
  lines 676-691.

## Checked local controls

- `canonical_statement.txt` is a byte-exact copy of
  `local:pi-lacunary-near-return-sparsity`, SHA-256
  `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
- T64 checked module: `knowledge_library/t64/AggregateFejerCriterion.lean`,
  SHA-256
  `ce4dac5fbb5ab1e7dd539e8dcc81a2c58351d4078e8e30ca774e30fea612ab16`.
  Controlling locators are lines 1482-1511, 1541-1598, 1633-1720,
  1741-1757, and 1843-1924.
- T107 checked module:
  `knowledge_library/t107/T107AveragedTriangularFejer.lean`, SHA-256
  `45cb809d65c38b866ad7c46c913d617c61f8e97e777ccdec8ed9645e4982ae28`.
  Controlling locators are lines 31-69, 88-113, and 150-172.
- Accepted T116 comparison control: `t116-report.md`, a byte-exact vendored
  copy of the accepted report, SHA-256
  `573011bda281022483a113829138112494b73d667323c30aa2a0ef03bba32cd1`.
  Its scope and candidate inventory are at lines 15-25 and 73-95; its
  prior-fingerprint table is at lines 552-595; its unproved fixed-pi transfer
  premise and scope firewall are at lines 597-624. This local control is not a
  primary source and does not change either cap.
- The terminal semantic obstruction memory was consulted only as an unverified
  ledger. Its SHA-256 is
  `aa8b0f84010f2850807e383e21f45dcb9c0dc548b5e22e0c3c4cd2779528f76f`.

No retrieval failed. No source claims a result about the prescribed fixed
decimal orbit. Source statements are `literature-checked`; substitutions and
transfers in `REPORT.md` are separately labeled `proof sketch`.
