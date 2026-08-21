# T60 source manifest

Accessed: 2026-08-02 UTC.

The canonical problem is locally formulated and has no original source URL.
Its byte-exact copy and hash are recorded below. This is a bounded audit of the
already source-pinned inputs requested by T60, not a novelty search.

| ID | Source and URL | SHA-256 | Exact use and locator |
|---|---|---|---|
| Canonical | `knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt`; no external URL | `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6` | Exact canonical question and recorded ambiguities. |
| V85 | J. D. Vaaler, *Some extremal functions in Fourier analysis*, Bull. AMS 12 (1985), 183-216, DOI <https://doi.org/10.1090/S0273-0979-1985-15349-2> | PDF `e606ccef342e72d7e48b59a7da7f8577f72fd351ce32989b23dd85e9e8cd4c1a` | Midpoint normalization (1.16), pp. 186; transform (2.28), p. 192; periodic Fejer kernel and sawtooth (6.5)-(6.6), p. 206; periodic approximation Theorem 18, especially (7.14), p. 210; BV specialization Theorem 19, (7.24)-(7.27), pp. 211-212. |
| ZZ20 | D. Zeilberger and W. Zudilin, *The irrationality measure of pi is at most 7.103205334137...*, Moscow J. Comb. Number Theory 9 (2020), 407-419, DOI <https://doi.org/10.2140/moscow.2020.9.407> | PDF `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5` | Definition and quantifiers, printed p. 407; Propositions 7-8 and equation (18), pp. 417-418; final exponent `7.10320533413700172750577342281...`, p. 418. |
| T56 | Accepted kernel module inspection copy | `41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc` | Exact sparse short-sector endpoints and target predicate. |
| T58 | Accepted kernel module inspection copy | `04b3808f208db000284cf369467f4d2ffb907b1af44b30fcada8451b8503016d` | Exact positive-frequency and triangular rectangle endpoints. |

`vaaler-1985.txt` is the retained `pdftotext` extraction inherited with the
pinned V85 source. `zeilberger-zudilin-2020.txt` was generated locally with
`pdftotext -layout`. The PDFs, not extracted text, are authoritative where
layout or OCR is ambiguous.

The Vaaler scan/OCR is visually ambiguous in one equality-characterization
line following (7.16), but T60 uses only the unambiguous inequality (7.14) and
derives its specialization directly.
