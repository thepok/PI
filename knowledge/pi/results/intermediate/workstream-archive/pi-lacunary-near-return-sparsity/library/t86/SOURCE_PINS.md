# T86 source pins

Audit date: 2026-08-09 UTC.

## Scope and count

This audit retains exactly four primary sources for exactly three candidates.
The six vendored Lean files are accepted local frontier interfaces, not
additional literature sources. Crossref, OpenAlex, DOI landing pages, and the
accepted local inventory were searched on the audit date. The search was
bounded rather than claimed exhaustive.

## Canonical statement

- Local source URL: `local:pi-lacunary-near-return-sparsity`.
- Delivered byte-exact file: `canonical_statement.txt`.
- SHA-256:
  `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
- Canonical question: line 2.
- Provenance: line 5.
- Ambiguities A1--A16: lines 7--23.

## S1: effective times-2, times-5 dynamics

Jean Bourgain, Elon Lindenstrauss, Philippe Michel, and Akshay Venkatesh,
"Some effective results for x a x b," *Ergodic Theory and Dynamical Systems*
29 (2009), 1705--1722.

- DOI: <https://doi.org/10.1017/S0143385708000898>.
- Publisher PDF URL:
  <https://www.cambridge.org/core/services/aop-cambridge-core/content/view/01225FAD40EEBC38F3AE1A5C119D0267/S0143385708000898a.pdf/div-class-title-some-effective-results-for-span-class-italic-a-span-span-class-italic-b-span-div.pdf>.
- Delivered PDF: `blmv-2009.pdf`.
- PDF SHA-256:
  `372d251b5c7c4936ab4e6b9cc6fb3af2ded2c8fe81020ad3e467843c20878e3b`.
- Theorem 1.4: printed p. 1706, PDF p. 2. It assumes multiplicatively
  independent `a,b`, `H_mu(P^N) >= rho log N`, `N>N0(a,b)`,
  `delta<=rho/20`, and nonnegative `f in C^1`; it selects
  `m=a^s b^t<N` and gives equation (1.4a).
- Corollary 1.6: printed p. 1707, PDF p. 3. It records interval proportions
  and density for a finite invariant set.
- Theorem 1.8: printed p. 1707, PDF p. 3. If `a,b` are multiplicatively
  independent and an irrational `alpha` satisfies
  `|alpha-p/q|>=q^(-k)` for every `q>=2,p in Z`, then
  `{a^s b^t alpha : s,t<=N}` is `(log log N)^(-kappa_6)`-dense for
  `N>=N0(k,a,b)`.

## S2: effective irrationality measure of pi

Doron Zeilberger and Wadim Zudilin, "The irrationality measure of pi is at
most 7.103205334137...," *Moscow Journal of Combinatorics and Number Theory*
9 (2020), 407--419.

- DOI: <https://doi.org/10.2140/moscow.2020.9.407>.
- Publisher PDF URL:
  <https://msp.org/moscow/2020/9-4/moscow-v9-n4-p06-s.pdf>.
- Delivered PDF: `zeilberger-zudilin-2020.pdf`.
- PDF SHA-256:
  `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`.
- Definition: printed p. 407, PDF p. 2, introduction. For every positive
  epsilon and all sufficiently large denominators, the defining lower bound
  holds for every integer numerator.
- Propositions 7 and 8: printed p. 417, PDF p. 12, supply the integral linear
  forms and asymptotics.
- `World record`: printed p. 418, PDF p. 13, gives
  `mu(pi)<=7.10320533413700172750577342281...<36/5`.
- The source gives no numerical eventual denominator threshold.

## S3: Hata complex-integral approximants

Masayoshi Hata, "Rational approximations to pi and some other numbers,"
*Acta Arithmetica* 63 (1993), 335--349.

- DOI: <https://doi.org/10.4064/aa-63-4-335-349>.
- Publisher PDF URL:
  <https://www.impan.pl/shop/publication/transaction/download/product/107787?download.pdf>.
- Delivered PDF: `hata-1993.pdf`.
- PDF SHA-256:
  `c3294d1987dfd013ec4d13f93737233177817d50c9c102ea95033e986cd9e3df`.
- Equations (1.3)--(1.4): printed p. 336, PDF p. 2, define the complex
  integral and rational function.
- Theorem 1.1: printed pp. 336--337, PDF pp. 2--3. For every epsilon>0,
  all sufficiently large `H=max(|q|,|r|)` satisfy the stated lower bound for
  `p+q*pi+r*log 2`; the exponent is `7.016045...`.
- Lemma 2.2, equations (2.2)--(2.3): printed pp. 339--340, PDF pp. 5--6,
  defines the denominator multiplier and its asymptotic exponent `kappa`.
- Equation (3.1): printed p. 343, PDF p. 9, expands the integral.
- Printed pp. 344--345, PDF pp. 10--11: defines Gaussian integers
  `p_n,q_n,r_n`, the relation `q_n*pi-p_n=epsilon_n`, and positive constants
  `sigma,tau` with `log|q_n|/n -> sigma` and
  `log|epsilon_n|/n -> -tau`; the proof gives `sigma/tau=7.016045...`.

## S4: Wallis sequence

Long Lin, Ji-En Deng, and Chao-Ping Chen, "Inequalities and asymptotic
expansions associated with the Wallis sequence," *Journal of Inequalities and
Applications* 2014:251.

- DOI: <https://doi.org/10.1186/1029-242X-2014-251>.
- Publisher PDF URL:
  <https://journalofinequalitiesandapplications.springeropen.com/counter/pdf/10.1186/1029-242X-2014-251>.
- Delivered PDF: `lin-deng-chen-2014.pdf`.
- PDF SHA-256:
  `a39419718fa55af6d4ec64ce8bc833a0fc6b11a983a7df162546a387e3fc4b49`.
- Equations (1.1)--(1.2): PDF p. 1, define
  `W_n=prod_{k=1}^n 4k^2/(4k^2-1)` and `W_n -> pi/2`.
- Equation (1.3): PDF p. 1, records Brouncker's continued fraction.
- Equations (3.8)--(3.11): PDF pp. 4--5, give the asymptotic expansion; in
  particular `W_n=(pi/2)(1-1/(4n)+5/(32n^2)+O(n^-3))`.
- Theorem 1, equations (3.12)--(3.13): PDF pp. 5--6, gives the general
  asymptotic expansion and explicit coefficients.

## Accepted local frontier pins

These files are vendored byte-for-byte. Their declarations are machine-checked
accepted interfaces, but their cancellation/compatibility hypotheses are not
claims about pi unless their theorem types say so.

| item | file | SHA-256 | exact locator |
|---|---|---|---|
| T7 | `T7FiniteCylinderEnergy.lean` | `cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c` | comparison lines 294--318; exact frontier lines 348--386 |
| T10 | `T10LongLagResonance.lean` | `63ccfd2417aca055ef9071e03b70092acb1fee26a279db6c5c35c9295aa91947` | resonance lines 626--690; literal not-C1 output lines 832--894 |
| T28 | `T28AdjacentNodeCompatibility.lean` | `f94c5c2060be43f0800e83adb782b5f3d20ee3fff7beadd2d28c9e92cc818dbd` | predicates lines 91--122; contradiction lines 392--451; conditional bridge lines 456--492 |
| T55 | `T55SignedMultiplierTenPairing.lean` | `025f3f7095f18bc542797113073d2bb20921895582dd49eb553b415952f31ffd` | top-shell predicate lines 568--579; implications lines 582--691 |
| T61 | `T61DirectLabelAdjacentPhaseVariance.lean` | `2eaecb2df11027d6ed5911a16fe571b042afbe42e18daf57eaaffc668f74dbdb` | variance predicate and implications lines 344--418 |
| T64 | `T64AggregateFejerCriterion.lean` | `ce4dac5fbb5ab1e7dd539e8dcc81a2c58351d4078e8e30ca774e30fea612ab16` | orders lines 1416--1424; remainder lines 1716--1757; row theorem lines 1847--1924 |

## Prior semantic-inventory pins

These reports remain in the record's accepted knowledge library. They are
comparison inventory, not extra primary sources. A `proof sketch` row is never
used as a discharged mathematical premise in T86.

| item | verification level used here | knowledge-library path | SHA-256 | exact fingerprint locators |
|---|---|---|---|---|
| T63 | literature-checked applicability audit | `knowledge_library/t63/REPORT.md` | `28e7bdc28628404532afcecda50ed954836df3eb7d6578315604907a7f10ad59` | source statements 60--297; literal T55/T61 targets 299--444; terminal obstruction 765--807 |
| T68 | machine-checked route theorem; prose companion | `knowledge_library/notes/t68/REPORT.md` | `2f406533d202ab9ec1bd570bdeb07ef51b5e24d69d8d3143add508414a333f14` | exact decomposition 33--61; applicability 63--81; contradiction 83--99; Lean source is `knowledge_library/t68/CorrectedZudilinTransient.lean`, SHA-256 `c0076582b930b24adf29d84e84526fa9db0c28a9f20309cf4808ded31ec69479` |
| T78 | proof sketch; source audit literature-checked | `knowledge_library/notes/t78/REPORT.md` | `26cc36a18ea585d85d5e7f2c23e40df61bbb1ca94639541736531feb8074af4b` | transfer 377--453; order/occupancy 455--679; family-specific scale obstruction 742--949 |
| T79 | proof sketch | `knowledge_library/t79/REPORT.md` | `7fb415a8140597f5a061b945df08eacc122e693d4998fafca98ff98aa641d800` | exclusions 28--39; transfer/order 87--177; stated-range T10 comparison 179--235 |
| T80 | proof sketch; primary source pinned | `knowledge_library/notes/t80/REPORT.md` | `df86924ccf631ded30bb887e2d8a7ff6d0abfa2d5da5f0240221d526d85cbad5` | denominator ideal 199--326; coefficient versus real orbit 328--442; T10 map 444--555 |
| T81 | proof sketch using machine-checked T73/T28 inputs | `knowledge_library/notes/t81/REPORT.md` | `73b4198003d637e5b7277dbdfe05e4f2606613f8e906860243331a293dd3b77f` | statuses 71--103; packing 341--475; missing T28 criteria 477--544 |
| T82 | proof sketch using machine-checked T64 input | `knowledge_library/notes/t82/REPORT.md` | `d06801d820c9fd28286a48cdd7a2108a84db70de2561864979aa4dfc982f0ced` | carry operator 280--349; factor-10 obstruction 351--440; T64 map 442--579 |
| T85 | proof sketch adversarial correction | `knowledge_library/notes/t85/REPORT.md` | `06fc459ab48d1d3cbe78a3038bdc76e20591ee86b7d243cba4a879a1e1fce2c7` | tie audit 73--177; empty post-transient tail 233--367; qualified logarithmic frontier 404--519 |

## Retrieval and extraction

All four PDFs were retrieved or byte-reused on 2026-08-09. Text locators were
checked with:

```text
pdftotext -layout FILE.pdf FILE.txt
```

The verifier repeats extraction to temporary files and checks identifying
anchors. PDF hashes, not extraction bytes, are the source pins.
