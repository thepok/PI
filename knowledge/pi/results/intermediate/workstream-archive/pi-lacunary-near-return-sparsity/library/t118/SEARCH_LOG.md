# T118 bounded search log

Search date: 2026-08-10 UTC.

`SEARCHED_PRIMARY_SOURCE_COUNT: 4`

The search was intentionally bounded to the four primary PDFs listed in
`SOURCE_PINS.md`. All were opened and their theorem pages inspected. No search
result title, abstract-only result, or secondary citation is counted.

| lane | query/fingerprint | inspected source | decision |
|---|---|---|---|
| general and prime-power modulus | pointwise incomplete powers modulo composite or prime power; order completion | Bailey--Crandall Lemmas 4.3-4.5 and Theorem 4.6 | retain Lemma 4.5 as mechanism M1; exact Lemma 4.3 substitution gives `c1(P_r)=P_r`, so M1 fails before its bound; Theorem 4.6 is only a fixed-tower comparator |
| ordered prime prefix | incomplete exponential sums over `g^j`, prescribed nonzero character | Kerr Theorem 2 | retain as M2 |
| sum-product | pointwise incomplete power-residue sums with large order | Bourgain Theorem 3.2 | retain as M3 |
| transfer scale | accepted upper bound for the irrationality exponent of pi | Zeilberger--Zudilin definition and final bound | retain as scale input, not a cancellation mechanism |

The three retained mechanisms exhaust the candidate cap. A complete-subgroup
card was not added: Kerr's introduction and Theorem 3 already record the
completion scale, while the supplied T105 audit had separately pinned the
Di Benedetto et al. complete-subgroup theorem. Adding it would repeat the same
failure `L=ord_p(10)>p^(1/4)` and would not test a new T118 hypothesis.

The supplied library was searched before source selection. In particular,
T63, T68, T78, T79, T85, T87, T104, T105, T113, T114, T115, T116, T64, T107,
and the obstruction memory were inspected. The accepted T116 report (SHA-256
`573011bda281022483a113829138112494b73d667323c30aa2a0ef03bba32cd1`) is
vendored as `t116-report.md`; its computable variable-depth avoidance selector
for an artificial sibling point is disjoint from T118's fixed-numerator
private-prime-power modular cancellation audit. The T109 content is available
only as a secondary fingerprint in the T113 note. No readable T117 artifact
was supplied, so the report records that inspectability limit without
inventing a comparison.

No novelty beyond this bounded corpus is claimed. The nearest fingerprint is
T87's exact-numerator/conductor card, followed by T105's prescribed-character
logarithmic modular card and T85's special-numerator gap.
