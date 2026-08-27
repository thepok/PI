# T99 source manifest

Accessed and checked: 2026-08-09 UTC.

The PDFs are authoritative. Text files were produced by `pdftotext -layout`
and are locator aids. `verify.sh` checks all byte hashes and the anchors used
by the audit from a directory containing only delivered artifacts.

## Canonical and checked local inputs

| ID | File | SHA-256 | Exact use |
|---|---|---|---|
| Canonical ENT/C1 | `pi-positive-decimal-factor-entropy.txt` | `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6` | Locally formulated; no original source URL. Literal C1/ENT and ambiguities, lines 1--28. |
| Canonical LL context | `pi-decimal-factor-complexity.txt` | `e2b6c9375936a97fe6cdd10c3f014613267f3c491935b536c6ec016c5f501e43` | Locally formulated; no original source URL. Morse--Hedlund baseline, lines 1--13. |
| T36 | `T36DecimalPeriodicWindowGap.lean` | `900e9fdeefbaea73236435b3845cd9dcc3c3b07b93d2e244b94dc39f4c109781` | `machine-checked`; exact window definition lines 42--45, effective irrationality lines 65--69, and window gap lines 265--305. |
| T2 | `T2ExponentialCollisionCriterion.lean` | `608e959dcbb2114c7102ca7d06ae0b16c8c6309c7f994e25c372c495b00f0fac` | `machine-checked`; literal C1/C2 lines 25--41 and `C2 => C1` lines 120--143. |

## Primary source S1: Zeilberger--Zudilin

- Authors: Doron Zeilberger and Wadim Zudilin.
- Title: *The irrationality measure of pi is at most 7.103205334137...*.
- Publication: Moscow Journal of Combinatorics and Number Theory 9 (2020),
  407--419.
- DOI: <https://doi.org/10.2140/moscow.2020.9.407>.
- Retrieved PDF URL:
  <https://msp.org/moscow/2020/9-4/moscow-v9-n4-p06-s.pdf>.
- Retained PDF: `zeilberger-zudilin-2020.pdf`.
- PDF SHA-256:
  `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`.
- Text SHA-256:
  `49ca4907538e4ccea23cee27f051f5b33832ed2cf3e3093b4aab58a13c814a68`.
- Exact locators: definition and quantifier convention, printed p. 407
  (PDF p. 2); Propositions 7--8, printed pp. 417--418 (Propositions begin on
  PDF p. 12); final value `7.10320533413700172750577342281...`, printed
  p. 418 (PDF p. 13).

## Primary source S2: Bugeaud--Kim

- Authors: Yann Bugeaud and Dong Han Kim.
- Title: *A new complexity function, repetitions in Sturmian words, and
  irrationality exponents of Sturmian numbers*.
- Version: arXiv:1510.00279v3, 23 August 2017; published in Transactions of
  the American Mathematical Society 371 (2019), 3281--3308.
- Versioned record: <https://arxiv.org/abs/1510.00279v3>.
- DOI: <https://doi.org/10.1090/tran/7378>.
- Retrieved PDF URL: <https://arxiv.org/pdf/1510.00279v3>.
- Retained PDF: `bugeaud-kim-1510.00279v3.pdf`.
- PDF SHA-256:
  `008d909f11d3d549592945735bfd442cb758452ac8b476c2863890ea6d5ea211`.
- Text SHA-256:
  `e0b42e3b1bc434b1202ca330477ea5935529a4994fcc9a50287ddee171675d06`.
- Exact locators:
  - `p(n,x)` and Morse--Hedlund Theorem 1.1, PDF pp. 1--2;
  - `r(n,x)`, PDF p. 2;
  - Lemma 2.2 and Theorem 2.3, PDF p. 4;
  - Fibonacci word is Sturmian, PDF p. 5;
  - Definition 3.2 of `rep`, PDF p. 6;
  - `rep(f)=phi`, PDF p. 7;
  - Definition 4.1, PDF p. 8;
  - Theorem 4.2, PDF p. 9.

## Primary source S3: Mignosi--Pirillo

- Authors: Filippo Mignosi and Giuseppe Pirillo.
- Title: *Repetitions in the Fibonacci infinite word*.
- Publication: RAIRO Informatique theorique et applications 26 (1992),
  199--204.
- DOI: <https://doi.org/10.1051/ita/1992260301991>.
- Archival record: <https://www.numdam.org/item/ITA_1992__26_3_199_0/>.
- Retrieved PDF URL:
  <https://www.numdam.org/item/ITA_1992__26_3_199_0.pdf>.
- Retained PDF: `mignosi-pirillo-1992.pdf`.
- PDF SHA-256:
  `96e3bca270ea1a52671670757e39b31be97ad1eec194d2321d241e5be253bfe1`.
- Text SHA-256:
  `14b77000d625a1117fced25b62453b69df07ec58adcb31d69028d85cbce90c37`.
- Exact locator: printed p. 200, PDF p. 3, defines the Fibonacci word by
  iterating `psi(a)=ab`, `psi(b)=a` from `a`. The scan's extracted text omits
  parts of the displayed morphism; the retained PDF is authoritative and the
  formula was checked visually.

## Search and retrieval limitations

- Exact arXiv API queries and their dispositions are recorded in Section 7 of
  `T99_DELTA_AUDIT.md`.
- OpenAlex and Semantic Scholar returned HTTP 429 on 2026-08-09.
- No theorem from an unretrieved or unretained source is used.
- S3 is a scan with imperfect OCR. Only the visually checked morphism display
  is used; no OCR-only formula is authoritative.
