# T5 source and accepted-audit manifest

Retrieval date: 2026-07-23 UTC.

The authoritative byte pins for the files in `sources/` are in
`SHA256SUMS`. All PDFs were retrieved from the URLs below. Exact statements
were checked against the listed pages and against the accepted adjacent audits
in the second table. This is a bounded corpus, not an exhaustive literature
search.

## Primary Sources

| ID | Source, DOI or stable record, retrieval URL | Retained SHA-256 | Exact locator used |
|---|---|---|---|
| AB07 | B. Adamczewski and Y. Bugeaud, *On the complexity of algebraic numbers I. Expansions in integer bases*, Ann. Math. 165 (2007), 547-565. DOI <https://doi.org/10.4007/annals.2007.165.547>. PDF <https://annals.math.princeton.edu/wp-content/uploads/annals-v165-n2-p04.pdf>. | `55da32c4712b193ffee370af434a98d08ae5922e4731af1cb46a1a44212a83ec` | Definition of `p(n)` and Theorem 1, printed pp. 549-550. |
| EG-I | P. Erdos and I. S. Gal, *On the law of the iterated logarithm. I*, Proc. Koninklijke Nederlandse Akademie 58 (1955), 65-76. DOI <https://doi.org/10.1016/S1385-7258(55)50010-2>. PDF <https://www.renyi.hu/~p_erdos/1955-06.pdf>. | `a94e2560d886e4de674f678363c596276c73e0e06a492a866239543dee746931` | Main theorem, printed p. 65. |
| EG-II | P. Erdos and I. S. Gal, *On the law of the iterated logarithm. II*, Proc. Koninklijke Nederlandse Akademie 58 (1955), 77-84. DOI <https://doi.org/10.1016/S1385-7258(55)50011-4>. PDF <https://www.renyi.hu/~p_erdos/1955-07.pdf>. | `c638ec58e455da94a2406b858e0a5b9ce3271954e77c38eec10581abf0ed7ff6` | Completion of the proof of the Part I main theorem, Part II Sections 3-4, printed pp. 77-84. |
| PH75 | W. Philipp, *Limit theorems for lacunary series and uniform distribution mod 1*, Acta Arith. 26 (1975), 241-251. DOI <https://doi.org/10.4064/aa-26-3-241-251>. PDF <https://www.impan.pl/shop/publication/transaction/download/product/100600?download.pdf>. | `4d0edc8170fe1ddf368ada0fd64ed7ec48411840ab6c07fdd658e44fbae84e3a` | Theorem 1, printed pp. 241-242; deterministic inequality (3.9) and note added, printed p. 250. The PDF is an image scan; these locators require visual checking. |
| FU08 | K. Fukuyama, *The law of the iterated logarithm for discrepancies of {theta^n x}*, Acta Math. Hungar. 118 (2008), 155-170. DOI <https://doi.org/10.1007/s10474-007-6201-8>. Repository record <https://hdl.handle.net/20.500.14094/90003836>. PDF <https://da.lib.kobe-u.ac.jp/da/kernel/90003836/90003836.pdf>. | `4f06dbbab6f877e4e1a99a73d0f858117f5af5bcb84c9843fd9abdda0f774f24` | Theorem and Corollary (4), journal pp. 155-156. Corollary (4) gives the displayed general formula for even integer `p>=4`; `sqrt(220)/27` is the audit's explicit `p=10` substitution, not text printed separately by the source. |
| SZ47 | R. Salem and A. Zygmund, *On Lacunary Trigonometric Series*, PNAS 33 (1947), 333-338. DOI <https://doi.org/10.1073/pnas.33.11.333>. PDF <https://europepmc.org/articles/PMC1079068?pdf=render>. | `5c9a042807dab935ab49179bfbfd765dc5f2416873cabf60d2886a7fc2cee604` | Complex-coefficient distribution result (vi), printed p. 337. The scan has OCR errors; the PDF is authoritative. |
| RZ99 | Z. Rudnick and A. Zaharescu, *A metric result on the pair correlation of fractional parts of sequences*, Acta Arith. 89 (1999), 283-293. DOI <https://doi.org/10.4064/aa-89-3-283-293>. PDF <https://www.impan.pl/shop/publication/transaction/download/product/110756?download.pdf>. | `d16de4bd2990cf6d022c9e49fff5ae59493a651db2690c74ec8aacbfc36a293f` | Definition (1.1), printed p. 283; Theorem 1, Proposition 2, and Corollary 3, printed p. 284. |
| RZ02 | Z. Rudnick and A. Zaharescu, *The distribution of spacings between fractional parts of lacunary sequences*, Forum Math. 14 (2002), 691-712. DOI <https://doi.org/10.1515/form.2002.030>. Version record <https://arxiv.org/abs/math/9912103v1>. PDF <https://arxiv.org/pdf/math/9912103v1>. | `4e05292f2d3541e93dd1085cb0ebbf9aded0a53358bf1410feecd0535bdb64cb` | Theorems 1.1-1.2, preprint pp. 1-3; Lemma 3.1, pp. 10-11; Proposition 4.1, p. 11. |
| BBP97 | D. Bailey, P. Borwein, and S. Plouffe, *On the Rapid Computation of Various Polylogarithmic Constants*, Math. Comp. 66 (1997), 903-913; NASA report version. DOI <https://doi.org/10.1090/S0025-5718-97-00856-9>. PDF <https://ntrs.nasa.gov/api/citations/19970009337/downloads/19970009337.pdf>. | `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4` | Theorem 1 and the base-16 identity, local report p. 3; digit-extraction algorithm, Section 3, local report pp. 7-8. |
| BC02 | D. Bailey and R. Crandall, *Random Generators and Normal Numbers*, Experimental Math. 11 (2002), 527-546. DOI <https://doi.org/10.1080/10586458.2002.10504704>. PDF <https://www.davidhbailey.com/dhbpapers/bcnormal-em.pdf>. | `9d1510fc72b6298295a3f10ca6d314936d083bc698982e0386e02bd8c9d9108f` | Hypothesis 3.1 and conditional Theorem 3.3, journal p. 531 (local PDF p. 5). |
| ZZ20 | D. Zeilberger and W. Zudilin, *The irrationality measure of pi is at most 7.103205334137...*, Moscow J. Comb. Number Theory 9 (2020), 407-419. DOI <https://doi.org/10.2140/moscow.2020.9.407>. PDF <https://msp.org/moscow/2020/9-4/moscow-v9-n4-p06-s.pdf>. | `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5` | Definition and bound, printed p. 407; Propositions 7-8 and final exponent, printed pp. 417-418. |

### Mutable-source note

The Kobe repository dynamically regenerates or re-encrypts the FU08 PDF. The
accepted T28 audit retained PDF hash
`59b263e7d74aa627606181646c75c02803c41d42af4d1780f7ff8de28f917266`
and documented later fresh hashes with identical extracted mathematical text.
This delivery retains the actual bytes retrieved on 2026-07-23 under the new
hash shown above. No equality with the older PDF-byte pin is claimed.

## Reused Accepted Audits

The delta audit relies on these content-addressed accepted artifacts instead
of repeating their full surveys. The `verify.sh` script always checks every
retained source and audit artifact. When a project checkout is discoverable,
it additionally checks every referenced proof-ledger object and formal
dependency; those accepted objects are deliberately not recopied here.
The acceptance receipts use `verdict: done`; their automatic
`claim_label_suggestion` is not used as a mathematical label.

| Program/item | Audit SHA-256 | Manifest or corpus SHA-256 | Acceptance receipt SHA-256 | Reused scope |
|---|---|---|---|---|
| pi decimal factor complexity T2 | `54d0dca52b5640c1030714cdf58e3cb5f12ac16a2a3dd90c407e3b41bd96443a` | `9e24221a6578169d22f85cb9a3245cf0a23ae0cda11304a0435716be6e2fd0fa` | `1aed7541bb15deec6489fd633ce1003214a769834b688d04d808bc4a30942b9d` | AB07 factor complexity and pi algebraic/transcendental mismatch. |
| pi decimal factor complexity T11 | `8661237d2363358c4f2328fb974c693b5f2abaff40470a9eb8340cece34a4b4f` | `caf0f52164d53e5e965ae0523fda342b6f34f52d6ab63d16f0361048ea2cd6e7` | `dafd9dadcac2279f02d3d2d2930405e59955f2379da13f84f2a30cc6abb2af58` | Exact HFE weights, quantifiers, and source applicability. |
| pi digits T28 | `4845c8661303b873bc4bb38dc8ee1005695fdd62b1fe4d16b36eaee61244abbd` | `33c0ccc0cba5f8aaa12783e5201da41ffa002d0ea01cdd21621791b8b28e6544` | `5984f0dacb05f4bfc3e612836edc4560a6965c02ccce18ddc9e18b043d4ab401` | EG, Philipp, and Fukuyama source transcriptions and metric/fixed-point distinction. |
| pi lacunary near-return sparsity T3 | `1508a10c2a9ec6dd5a4f3400c40e912e7a9c4e5e95a010d8065ca54744145548` | source archive `35ace6757dba2f6defc0f3d4402eb24e53ef834a34aff6f6a3ff279be8b15583` | `04b55c7c6a716e23cceac8d22f545a5e4763f6a40dbe2ea22b1a7085d0e35db4` | RZ pair-correlation hypotheses, target normalization, and fixed-pi gap. |
| pi digits T6 | `bd95aa34c512ea934801d9baa2d574854ecbb4dc7575670fc4d8304637928f33` | pins embedded in audit | `8ca6c6555b6892a376ae5e313c13e3b09aa132d150e4eb471925fa864b75b631` | BBP digit extraction and Bailey-Crandall conditional route. |
| pi positive lower block density T24 | `fedbf2ae2f990ddd57442d240989f878be9db1868a0fde9b85534572cdfab0bd` | corpus `ba716f7deb6c82c33366cfb4f569c904d59d70283860a4ae7ab5e6be1c924b53` | `95a85aae4b6fc49b573292621f2fdb09052865594cdcc5f9f7bc154172cb0fd5` | Exact irrationality-measure substitution and aggregate-energy limitation. |

## Formal Dependency Pins

| Dependency | SHA-256 | Exact role |
|---|---|---|
| Canonical statement `knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt` | `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6` | Immutable C1 and ambiguity record. |
| Accepted T1 `CanonicalEntropy.lean` | `8f424db10d98a42ab0e547b2abdef0db9c5b45443c05a4e01033502a2934dbdf` | C1 normalization and entropy equivalence. |
| Accepted T2 `T2ExponentialCollisionCriterion.lean` | `608e959dcbb2114c7102ca7d06ae0b16c8c6309c7f994e25c372c495b00f0fac` | Exponential C2 and conditional C2-to-C1 bridge. |
| Accepted T3 `FiniteFourierObstruction.lean` | `5bb975c9107c5a1862e269b85a9797c195a6f96747b8f35c41e80e5de808c798` | Cell-label Fourier obstruction under failure of C1. |
| Accepted T4 `T4FinitePrefixMultiplicityTransfer.lean` | `af8fff5d30cb98164ba6730e457adc4de8c18b6f9944d16cb794f1c3cc60eb3c` | Covering-prefix coefficient/multiplicity-defect dichotomy. |
| Accepted `T10PiWeightedFourierReduction.lean` | `45003707a7b30447c9dd9ed5843f8c899a7c7107814c99f9b7a7a9f4ab8bf4ff` | Exact weighted HFE definition and its conditional polynomial near-return conclusion. |

## Retrieval Limitations

- PH75 and SZ47 are scans. Formulas at the cited printed pages were inherited
  from accepted visual audits and checked against the retained images; OCR is
  not treated as authoritative.
- FU08 changed byte hash on fresh retrieval as documented above.
- No cited source was omitted after retrieval failure in this bounded corpus.
