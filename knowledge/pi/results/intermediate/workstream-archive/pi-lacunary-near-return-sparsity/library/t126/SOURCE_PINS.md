# T126 source and comparison pins

Access date: 2026-08-10 UTC. The primary PDF and prior reports are vendored
byte-exactly. Prior prose is comparison memory only.

## Primary source

| ID | Source | Delivered file and SHA-256 | Exact locator used |
|---|---|---|---|
| S1 | Sandip Singh and T. N. Venkataramana, "Arithmeticity of Certain Symplectic Hypergeometric Groups," arXiv:1208.6460v2, https://arxiv.org/abs/1208.6460, PDF https://arxiv.org/pdf/1208.6460v2 | `singh-venkataramana-1208.6460v2.pdf`, `edc121df43a7921658c4e5ab4d728ad3021de746f9712ba5f92db933d0b0c1b3` | arXiv/PDF page 1 defines `theta=z d/dz` and `D=product(theta+beta_i-1)-z product(theta+alpha_i)`. T126 independently specializes this definition and compares coefficients; the recurrence is not quoted as a source theorem. |

## Immutable statement

| File | SHA-256 |
|---|---|
| `canonical_statement.txt` | `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8` |

## Prior fingerprints

| Item | Delivered file | SHA-256 | Regions used and level |
|---|---|---|---|
| T79 | `prior-T79-REPORT.md` | `7fb415a8140597f5a061b945df08eacc122e693d4998fafca98ff98aa641d800` | Sections 4--7, especially lines 116--235; unverified `proof sketch`, finite checks only. |
| T85 | `prior-T85-REPORT.md` | `06fc459ab48d1d3cbe78a3038bdc76e20591ee86b7d243cba4a879a1e1fce2c7` | Sections 3, 6, 8--9, especially lines 73--177 and 233--519; unverified `proof sketch`, replay `experiment`. |
| T112 | `prior-T112-REPORT.md` | `72884fc7d8d594cfd2f380cafde121c541c1aa316badf054ac143bb102abcefa` | Sections 4--7 and 11--12; source claims `literature-checked`, deductions `proof sketch`, replay `experiment`. |
| T118 | `prior-T118-REPORT.md` | `2ed7a176bedb2f3a1627dffd4002f6b6141f078fe5c73798041b4fba90c7410e` | Sections 2, 6--12; source claims `literature-checked`, deductions `proof sketch`, replay `experiment`. |
| T121 | `prior-T121-REPORT.md` | `01b97953941608b41b0fcd12cc5be0047f447be28d7cd26f8bae6506717e6cf2` | Sections 3, 5--10; source claims `literature-checked`, deductions `proof sketch`, replay `experiment`. |
| latest readable T123 | `prior-T123-REPORT.md` | `3eed848437e5ade5cfc0ac5c8f8fabf5968ff156262b74ea2d947413b74fecb2` | Sections 2--10; source claims `literature-checked`, deductions `proof sketch`, replay `experiment`; workflow result was `revise`, and its T121 availability row is stale in the current snapshot. |

No readable T125 report, source package, result, or content hash was available
in the binding T126 snapshot. Only active-task metadata was reported, so no
T125 fingerprint is inferred.
