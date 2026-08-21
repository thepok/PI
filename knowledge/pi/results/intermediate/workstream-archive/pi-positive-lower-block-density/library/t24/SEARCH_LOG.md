# T24 bounded search log

Search and retrieval date: 2026-07-23 UTC.

This is a finite applicability audit, not a claim that no other rational-
approximation theorem for pi exists.

## Search procedure

1. Imported T5's accepted bounded audit and its locked T9 and T11 evidence.
   Those audits already identify Salikhov and Zeilberger--Zudilin as genuine
   fixed-pi arithmetic inputs but not distribution theorems.
2. Followed the primary-source citation chain visible in the retained papers:
   Mahler (1953), Mignotte (1974), Hata (1993), Salikhov (2008), and
   Zeilberger--Zudilin (2020).
3. Retrieved and inspected exactly those five primary sources. This is below
   the six-source cap. Six result rows were retained, below the twelve-row cap.
4. Checked the theorem statements against the exact denominator
   `10^n*(10^r-1)` and against T23's all-`N`, all-`m`, every-`s<1` order.

## Retained endpoints

| Source | DOI | Retained PDF URL |
|---|---|---|
| Mahler | `10.1016/S1385-7258(53)50005-8`; reprint `10.4171/dms/8/31` | `https://ems.press/content/book-chapter-files/27418` |
| Mignotte | `10.24033/msmf.139` | `https://www.numdam.org/item/10.24033/msmf.139.pdf` |
| Hata | `10.4064/aa-63-4-335-349` | `https://www.impan.pl/shop/publication/transaction/download/product/107787?download.pdf` |
| Salikhov | `10.1070/RM2008v063n03ABEH004543` | `https://www.mathnet.ru/php/getFT.phtml?jrnid=rm&paperid=9175&what=fullteng&option_lang=eng` |
| Zeilberger--Zudilin | `10.2140/moscow.2020.9.407` | `https://msp.org/moscow/2020/9-4/moscow-v9-n4-p06-s.pdf` |

## Bounded exclusions

- The historical references named in the five retained papers were not all
  retrieved. The corpus deliberately stops at five direct pi sources rather
  than claiming an exhaustive history.
- Results about rational approximation to `pi^2` were not substituted for
  direct denominator-`q` results about `pi`.
- Generic almost-everywhere lacunary discrepancy papers were not repeated;
  they are already separated from fixed pi by accepted T5.

## Retrieval and inspection notes

- Salikhov's MathNet endpoint requires a browser user-agent and the MathNet
  landing page as referer. T24 imports T9's accepted PDF and text objects by
  content hash rather than retaining duplicate copies.
- Mignotte's old scan has usable text extraction, but superscripts in the
  theorem are garbled. The two inequalities were checked visually on printed
  p. 125 (PDF page 6); the PDF is authoritative.
- All other theorem locators were checked in both the retained PDF layout and
  the pinned `pdftotext -layout` output.
- No finite computation of pi digits was used.
