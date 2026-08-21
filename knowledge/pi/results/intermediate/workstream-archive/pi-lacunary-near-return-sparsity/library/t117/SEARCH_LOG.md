# T117 bounded search log

Search date: 2026-08-10 UTC.

The search was stopped after the load-bearing Legendre source and the primary
Weil mechanism source were retrieved. Two primary sources are below the cap of
six. One family is below the cap of two.

| Lane | Query or database | Outcome |
|---|---|---|
| symbolic collision theory | Crossref: `Legendre symbol pseudorandomness binary sequences` | located Mauduit--Sarkozy 1997, DOI `10.4064/aa-82-4-365-377`; publisher PDF retrieved |
| pattern distribution | Crossref/OpenAlex: `Legendre sequence pattern distribution` | located Ding 1998, DOI `10.1109/18.681353`; metadata says ideal short-pattern distribution, but the primary PDF was closed and was not used for any source claim |
| structured exponential sums | S1 references and exact theorem locators | S1 Theorem 2, Corollary 1, and Lemmas 1--3 give the needed character hypotheses and explicit complete bound |
| arithmetic finite-field Fourier decay | OpenAlex/Europe PMC for Weil, DOI `10.1073/pnas.34.5.204` | four-page primary scan retrieved from Europe PMC |
| local novelty | supplied T117 knowledge library and proof-ledger blobs, refreshed against accepted T114 SHA `db21ac7d0a7845264c727132293db149a06a832d6f67700fd9ceb0f69a142cca` and accepted T116 SHA `573011bda281022483a113829138112494b73d667323c30aa2a0ef03bba32cd1` | no inspected T89--T116 item has the complete Legendre subset-product-to-collision chain; T114's determinant/rank obstruction and T116's effective selector are distinct fingerprints |

## Retrieval blockers

1. Cunsheng Ding, *Pattern distributions of Legendre sequences*, IEEE
   Transactions on Information Theory 44 (1998), 1693--1698, DOI
   `10.1109/18.681353`: IEEE returned a bot challenge/error and OpenAlex and
   Semantic Scholar reported no open PDF. Only bibliographic metadata and the
   abstract were inspected. The paper is not counted in
   `PRIMARY_SOURCE_COUNT`, no theorem from it is labeled literature-checked,
   and it is not used as a premise.
2. Davenport's 1931 paper identified through S1/Ding metadata was paywalled.
   It was not needed after S1 supplied the exact specialized theorem and was
   not counted as an inspected primary source.
3. The first guessed PMC filename for Weil returned an HTML challenge. It was
   replaced by the verified Europe PMC PDF; the bad response is not delivered.

## Stop reason

S1 alone contains all hypotheses needed for the Legendre pattern calculation,
including the symbolic indicator expansion and shifted-product degeneracy
check. S2 pins the underlying primary square-root mechanism. Adding further
papers would not change the family, error scale, collision calculation, or
fixed-pi boundary.
