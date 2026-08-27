# T131 bounded search log

Search date: 2026-08-10 UTC.

The search was frozen at seven opened primary PDFs and three retained cards.
No source was added to fill the cap.

| order | lane and bounded query | opened source | decision |
|---|---|---|---|
| 1 | integral discrepancy: `totally unimodular linear discrepancy rounding circulation` | Doerr, *Linear Discrepancy of Totally Unimodular Matrices* | retain in C-TU; sharp coordinate rounding, but no mass or nesting statement |
| 2 | Euler ordering: `Eulerian digraph rotor router one Euler tour every edge` | Holroyd et al., *Chip-Firing and Rotor-Routing on Directed Graphs* | retain in C-EULER; exact at complete-tour endpoint |
| 3 | Euler-prefix discrepancy: `rotor walk stationary distribution explicit discrepancy K4` | Holroyd--Propp, *Rotor Walks and Markov Chains* | retain in C-EULER; growing-graph constant is the test obstruction |
| 4 | constructive pseudorandomness: `discrete low discrepancy sequence rational periodic rotor stack` | Angel et al., *Discrete Low-Discrepancy Sequences* | retain in C-EULER; local stacks only |
| 5 | coherent de Bruijn prefixes: `totally de Bruijn sequence prefix extension Euler path` | Fishman--Merrill--Simmons, *Uniformly de Bruijn Sequences...* | retain in C-NEST; literal nesting, exact uniform-flow special case |
| 6 | arbitrary-length balanced cycles: `arbitrary length de Bruijn floor ceil occurrences lift join` | Nellore--Ward, *Arbitrary-Length Analogs to de Bruijn Sequences* | retain in C-NEST; direct multidepth incidence balance, no literal prefix nesting across lengths |
| 7 | nested necklaces comparator: `nested perfect necklaces discrepancy log squared` | Becher--Carton, *Normal Numbers and Nested Perfect Necklaces* | retain in C-NEST only as the T122 duplication boundary |

The inspected sources cover four required domains: integral discrepancy; graph
circulations/Euler tours; constructive pseudorandomness; and symbolic collision
theory. Generic integer-programming proximity results were screened out before
opening because the totally-unimodular source gives the sharper relevant
coordinate result and the source cap rewards no redundant card.

The stop rule was reached when all four loss slots had a source-backed theorem
or a precise gap:

```text
rounding:       S1,
Euler ordering: S2--S4,
nesting:        S5--S7,
collision:      exact count algebra, compared with T121/T122.
```
