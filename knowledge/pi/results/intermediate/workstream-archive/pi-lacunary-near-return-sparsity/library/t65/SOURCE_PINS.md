# T65 source ledger

Checked: 2026-08-06 UTC.

No new retrieval was needed.  T65 starts from the byte-exact primary sources
retained by T63 and records the source-faithful Bailey--Crandall formula rather
than duplicating the PDFs.

## 1. Canonical statement

- Local source URL: `local:pi-lacunary-near-return-sparsity`.
- Project path: `knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`.
- SHA-256:
  `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
- Scope used: the canonical question remains the ordered,
  diagonal-inclusive fixed-pi question.  T65 audits only a proposed
  rational-phase route.

## 2. Zudilin version pair

1. Wadim Zudilin, *A BBP-style computation for pi in base 10*,
   arXiv:2409.10097v1, 16 September 2024.
   - Record: <https://arxiv.org/abs/2409.10097v1>
   - PDF: <https://arxiv.org/pdf/2409.10097v1>
   - DOI family: <https://doi.org/10.48550/arXiv.2409.10097>
   - PDF SHA-256:
     `67e8946c37b9e91da0dcdcc9f9886ef7278b69ca68200c7acac03197c9c59743`
   - `pdftotext -layout` SHA-256:
     `bc82ae9f327ef2533062d07216d94c092efec8128c733f526bccc3341ab41d79`
   - Locator: decimal paragraph and unnumbered decimal modular equality,
     PDF p. 3.

2. Wadim Zudilin, *A BBP-style computation for pi in base 5*,
   arXiv:2409.10097v2, 17 September 2024.
   - Record: <https://arxiv.org/abs/2409.10097v2>
   - PDF: <https://arxiv.org/pdf/2409.10097v2>
   - PDF SHA-256:
     `01ba3b7b1ebd22d0d718b0fa3ed67d20030870a2bfe41a3a6b3ff7a3ce479d25`
   - `pdftotext -layout` SHA-256:
     `73f138af3f4871548dcad600f862cf2bc6a84bc77548bbb95c4d0d549afa16c8`
   - Locators: equation (1), PDF p. 2; condition (2), equation (3), and
     Section 3, "An obvious flaw", PDF p. 3.

The version distinction is essential: v2 deletes the decimal claim and states
that the modular equality is incorrect when `2n+1>d-k`, with missing
denominator `5^(2n+1-d+k)m`.

## 3. Bailey--Crandall theorem

David H. Bailey and Richard E. Crandall, *Random Generators and Normal
Numbers*, Experimental Mathematics 11 (2002), no. 4, 527--546.

- DOI: <https://doi.org/10.1080/10586458.2002.10504704>
- Author PDF: <https://www.davidhbailey.com/dhbpapers/bcnormal.pdf>
- PDF SHA-256:
  `d6cb4c65494b8447428a480ba9c29139fcedfac47dc3fff029ec4a50a0d8db74`
- `pdftotext -layout` SHA-256:
  `bab7d90671a8c5384d4251b0516c4282554062cc4bd5cdcdc9d12dc02dafec47`
- Exact locator: Theorem 4.6 and proof, printed pp. 12--13; extracted text
  lines 621--645 in T63's retained text.

The primary theorem prints

```text
B (A c^(n/2) + J c^(-n/2)) log(c^n).
```

The logarithm multiplies both parenthesized terms.  This corrects the
transcription in T63 REPORT equations (3.17) and (7.5), where the logarithm
was attached only to the second term.

## 4. Reused machine-checked finite interfaces

The following accepted Lean sources are used only for their finite definitions
and identities.  No sketch-level prose premise is imported.

- T55 `SignedMultiplierTenPairing.lean` SHA-256:
  `025f3f7095f18bc542797113073d2bb20921895582dd49eb553b415952f31ffd`.
  Relevant declarations and locators: `triangularWeight`, `orbitCoefficient`,
  and `predecessorCoefficient`, lines 185--220; `endpointSum`,
  `terminalCorrelation`, and `endpointBudget`, lines 282--322;
  `stratumFejerSum_eq_endpoint_add_topShell` and
  `TopShellCorrelationHypothesis`, lines 539--579.
- T61 `DirectLabelAdjacentPhaseVariance.lean` SHA-256:
  `2eaecb2df11027d6ed5911a16fe571b042afbe42e18daf57eaaffc668f74dbdb`.
  Relevant declaration and proof locator:
  `DirectLabelAdjacentPhaseVarianceWithExactRemainder` and its threshold
  theorem, lines 340--389.
- T62 `ClosedExpansionPredecessorRegrouping.lean` SHA-256:
  `cef676197799dc7c3b8d93778ebf94c5a7c4bf1e88e8de17900c75762e47034e`.

T65 derives the displayed `S_J` rewrites directly from those finite sums.

## 5. Prior audit pins

- T63 `REPORT.md` SHA-256:
  `28e7bdc28628404532afcecda50ed954836df3eb7d6578315604907a7f10ad59`.
- T63 `SOURCE_PINS.md` SHA-256:
  `8087d065d6bb44f5f5e36b9d2a8fac0eae351196ba6fa421335f849776be1c34`.

T63 is used as a source locator and applicability audit.  All new arithmetic
claims needed by T65 are re-derived in `REPORT.md`; the corrected placement of
the logarithm is checked against the primary Bailey--Crandall source.
