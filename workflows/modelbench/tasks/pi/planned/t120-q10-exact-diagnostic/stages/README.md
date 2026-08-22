# T120 staged workflow

Status: planned and inactive. No file in this directory authorizes a
production index or window 13.

The stages form one fail-closed path:

1. `s0-controller-gate/` contains the controller-accepted pure schema and
   statistic validator. It does not authenticate T118 `r,w` provenance.
2. `s1-combined-term-generator/` specifies the independent combined-term
   generator route.
3. `s2-literal-four-pole-verifier/` specifies the physically disjoint literal
   four-pole verification route.
4. `a1-*` through `a4-*` specify four read-only reviews of separation,
   arithmetic/indexing, bytes/CAS/receipts, and decision/claim boundaries.
5. `t120-prew13/` may only record readiness for operator review after S0, S1,
   S2, a third controller-owned arithmetic route, tiny shards, hidden synthetic
   statistic tests, resource checks, and all four audits succeed.

The intended candidate allocation after executable controller gates exist is
four OpenRouter workers for S1, six OpenCode/Oxzen workers for S2, and four
OpenCode/Oxzen workers for the read-only audits. Candidate output never chooses
hashes, ranges, receipts, thresholds, or launch authority.
