# T133 primary-source pins

Access date: 2026-08-10 UTC.

```text
SEARCHED_DOMAIN_COUNT: 3
PRIMARY_SOURCE_COUNT: 3
```

## Immutable statement

| File | SHA-256 | Locator |
|---|---|---|
| `canonical_statement.txt` | `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8` | canonical question line 2; ambiguities lines 7--23; verification rules lines 25--26 |

## Primary sources

| ID | Domain | Bibliographic pin and URL | Delivered file and SHA-256 | Exact locator checked |
|---|---|---|---|---|
| S1 | hypergeometric arithmetic | Sandip Singh and T. N. Venkataramana, "Arithmeticity of Certain Symplectic Hypergeometric Groups," arXiv:1208.6460v2, <https://arxiv.org/abs/1208.6460>, PDF <https://arxiv.org/pdf/1208.6460v2> | `singh-venkataramana-1208.6460v2.pdf`, `edc121df43a7921658c4e5ab4d728ad3021de746f9712ba5f92db933d0b0c1b3` | PDF p. 1, paragraph beginning `Set theta`: `theta=z d/dz` and displayed `D=(theta+beta_1-1)...-z(theta+alpha_1)...`. The H1 specialization and recurrence in the report are deductions, not quoted source results. |
| S2 | automatic or regular sequences | Boris Adamczewski, Jason Bell, and Daniel Smertnig, "A Height Gap Theorem for Coefficients of Mahler Functions," arXiv:2003.03429v2, DOI <https://doi.org/10.4171/JEMS/1244>, abstract <https://arxiv.org/abs/2003.03429>, PDF <https://arxiv.org/pdf/2003.03429v2> | `adamczewski-bell-smertnig-2003.03429v2.pdf`, `c70932ece1c4cdcf5a62b39f91103c98841b3b958f3f622d58550322b9469353` | Printed pp. 8--9: Definition 3.3 defines the `k`-kernel; Definition 3.4 defines a linear representation; Theorem 3.5 states equivalence with `k`-regularity. Printed p. 9, paragraph before Definition 3.6 records Becker's implication that regular power series are Mahler. Printed p. 6, Example (g), records `sum v_p(n!) z^n` as p-regular, but T133 does not use that attribution as a premise. |
| S3 | Mahler functional equations | Dzmitry Badziahin and Evgeniy Zorin, "On the Irrationality Measure of the Thue--Morse Constant," arXiv:1707.06677v1, DOI <https://doi.org/10.1017/S0305004118000117>, abstract <https://arxiv.org/abs/1707.06677v1>, PDF <https://arxiv.org/pdf/1707.06677v1> | `badziahin-zorin-1707.06677v1.pdf`, `f8de296ba104cca97f4f6c3d45647e21c3db3d2207274facaf2c16b445483d15` | PDF pp. 2--3, equations (2)--(5): definition of Mahler functions; recurrences `t_(2n)=t_n`, `t_(2n+1)=1-t_n`; Thue--Morse product; exact equation `f_TM(z^2)=z/(z-1)f_TM(z)`. |

PDF extraction used `pdftotext -layout`. The replay extracts into a temporary
directory and checks bounded text anchors. Source semantics remain inspectable
in the pinned PDFs; extracted text is not itself a source pin.

No retrieval failed. No OCR was required.
