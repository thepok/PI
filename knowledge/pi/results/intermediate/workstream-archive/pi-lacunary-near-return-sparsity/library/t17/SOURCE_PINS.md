# T17 source pins and locators

Access date for all web sources: 2026-07-23 UTC.

## Proof source

Lorenz Milla, *A detailed proof of the Chudnovsky formula with means of basic
complex analysis*, arXiv:1809.00533v6 (2021),
<https://arxiv.org/pdf/1809.00533v6>.

- Retained PDF: `milla-1809.00533v6.pdf`.
- PDF SHA-256: `69e9513d3c03c7c5c5dce12b24187b2522e0f1b08d54266a15eef93a3421cd20`.
- `pdftotext -layout` extract: `milla-1809.00533v6.txt`.
- Extract SHA-256: `edf60a42b2e1c7dc56f3f5fd5175f381860d944d38a5ee131d0815e838ce5a83`.
- Theorem 0.1 (Main Theorem 9.7), PDF/printed p. 3: the general identity,
  with the explicit hypothesis `Im(tau) > 1.25`, definitions of `J` and `s2`
  immediately above it, and the principal square-root branch stated below it.
- Theorem 10.12, PDF/printed p. 44: the exact Chudnovsky formula used here.
  Its proof specializes Main Theorem 9.7 at
  `tau_163=(1+i*sqrt(163))/2`, uses the exact `J` and `s2` values from Tables
  10.1 and 10.2, and ends by multiplying by `545140134`.
- The hypothesis is satisfied because
  `Im(tau_163)=sqrt(163)/2 > 5/4`; both sides are positive real quantities and
  the displayed square roots therefore use the positive real branch.
- Chapter 10, especially Propositions 10.2-10.4 and Theorem 10.10, supplies
  exactness of the CM values. The author's footnote on p. 3 explicitly says
  this chapter cites external literature for the facts that the relevant
  `1728J(tau)` is integral and `s2(tau)` is rational. Thus the retained paper
  is a published proof with cited inputs, not a foundationally self-contained
  formal proof.

## Original publication and attribution

D. V. Chudnovsky and G. V. Chudnovsky, *Approximations and complex
multiplication according to Ramanujan*, in *Ramanujan Revisited*, Academic
Press (1988), pp. 375-472; reprinted in *Pi: A Source Book*, pp. 596-622,
DOI <https://doi.org/10.1007/978-1-4757-2736-4_63>.

- Retained Crossref response: `chudnovsky-crossref.json`, SHA-256
  `67f5af4ad7c4c5377c72762947d3e13a276605715b18c34a9ee3493a9ab089c2`.
- Original printed p. 389, reprint p. 610, equations (1.4)-(1.5).
  Equation (1.4) is the general CM identity; equation (1.5) is the `d=163`
  specialization with `640320` and `C1=13591409/545140134`.
- `chudnovsky-primary-formula.json` and
  `chudnovsky-primary-derivation.json` retain normalized Google Books search
  excerpts locating formula (1.5) and the preceding Clausen derivation on
  reprint p. 610. Their SHA-256 values are respectively
  `65b756cdb5019e09a6b2ade96668a03c9655553e52c123995e95e9e0ceac937b`
  and `11c5349c04a1dd142d81505631a334eec90b6dbf3dbe5d831228c2bed5a84729`.
- Those two OCR excerpts are approximate derived text, not substitutes for a
  page image and not the proof source used by this package. The full original
  scan is access-restricted. Milla Theorem 10.12 is the retained inspectable
  proof and itself cites the original equation as `[8, eq. (1.5)]`.

## T16 input provenance

- `t16-reproduce.sh` is the retained T16 retry-2 reproducer, SHA-256
  `6c53437a5ad492525ebe5f7316fefe8d4210d99a31772f36c5684db01a6c5ab8`.
  Lines 15-18 generate `1048596` fractional digits and byte-compare both the
  generated digit file and certificate with T16's delivered files.
- `t16-pi_certify.py` is the exact retained T16 retry-2 writer, SHA-256
  `e731865f0bf56a4acbff3035452537deb4d4e4d18a66faf781429ce8cb244ed9`.
  The T17 replay runs this writer at the T16 digit count and byte-compares its
  output with the independently enclosed T17 file.
- `t15-predecessor-SHA256SUMS.txt` is the retained predecessor manifest,
  SHA-256
  `789bae468b62efa0ecdfd44282d9f4020d5e93a664e5834b356a268ab12caf5d`.
  It is not mislabeled as a T16 manifest. Its line 10 independently fixes the
  same predecessor `pi_digits.txt` at
  `77eeccb0067283e14c460b33dc230de54ef15c2e825fc2a35c984fb6984bf684`.
- The file format reconstructed by both T16's writer and this package is
  exactly `1048596` ASCII fractional digits, without `3.` or wrapping,
  followed by one LF byte. Its payload-only SHA-256 is
  `677e20e8d4e416051786d608ba29f6c56b9c84d8bd48132e33f83e8663818989`.

## Canonical statement

The immutable statement is
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`, SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
It records no external source URL. T17 addresses only provenance of T16's
finite decimal input; it does not alter or resolve any quantifier in that
statement.
