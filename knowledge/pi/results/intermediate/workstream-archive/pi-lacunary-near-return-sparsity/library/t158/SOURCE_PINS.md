# T158 primary-source pins

Inspection date: 2026-08-12 UTC. Exactly four new primary papers were opened,
below the cap of eight. PDFs and their `pdftotext -layout` derivatives count as
one source. All four PDFs were text-readable; no OCR was used. Mathematical
locators use the page number displayed in the pinned PDF.

## S1: weighted de Bruijn Markov process

- Arvind Ayyer and Volker Strehl, *Stationary Distribution and Eigenvalues for
  a de Bruijn Process*.
- Version: arXiv:1108.5695v1, 29 August 2011.
- URLs: <https://arxiv.org/abs/1108.5695v1> and
  <https://arxiv.org/pdf/1108.5695v1>.
- Related DOI: <https://doi.org/10.1007/978-3-642-30979-3_5>.
- File: `ayyer-strehl-1108.5695v1.pdf`.
- SHA-256: `00d7ee6af00be2e35fd82165a4ca5cfb4373d3f59a2084de7f4f402448240e49`.
- Stable tuple: `arXiv:1108.5695v1|equations(2.2)-(2.5);Theorem3;Theorem12;Corollary13`.
- Exact locators: directed de Bruijn graph and Euler-tour correspondence, PDF
  p. 2; edge weights and continuous-time process, equations (2.2)--(2.5), PDF
  pp. 2--4; stationary vector, Theorem 3 and (3.18), PDF pp. 7--8;
  characteristic polynomial, Theorem 12 and (4.19), PDF p. 12; Bernoulli
  specialization, Corollary 13 and (5.1), PDF pp. 12--13.
- Scope: a random continuous-time Markov process on word states. It does not
  state that an arbitrary deterministic Euler tour with the same edge
  multiplicities is a sample from that process.

## S2: pseudo-spectral gap and random-trajectory concentration

- Daniel Paulin, *Concentration inequalities for Markov chains by Marton
  couplings and spectral methods*.
- Corrected version: arXiv:1212.2015v5, 13 November 2018; the abstract records
  that v5 repairs an incomplete argument in the previous version.
- URLs: <https://arxiv.org/abs/1212.2015v5> and
  <https://arxiv.org/pdf/1212.2015v5>.
- Journal DOI: <https://doi.org/10.1214/EJP.v20-4039>.
- File: `paulin-1212.2015v5.pdf`.
- SHA-256: `7a54a70c47954687e87800c5e7dcc9df37a47568ed13f35c5c170a5728d92a82`.
- Stable tuple: `arXiv:1212.2015v5|Assumption3.1;equations(3.1)-(3.3);Proposition3.4;Theorem3.11`.
- Exact locators: Assumption 3.1, PDF p. 12; reversible, absolute, and pseudo
  spectral gaps, equations (3.1)--(3.3), PDF pp. 13--14; mixing comparison,
  Proposition 3.4 and equations (3.9)--(3.12), PDF pp. 14--15; nonreversible
  Bernstein bound, Theorem 3.11 and (3.25)--(3.26), PDF p. 17. The periodic
  two-state warning distinguishing ordinary from absolute gap is PDF
  pp. 15--16.
- Scope: Assumption 3.1 requires a homogeneous irreducible aperiodic Markov
  chain; Theorem 3.11 concerns a stationary random trajectory. Its probability
  bound is not a pointwise theorem for a prescribed deterministic path.

## S3: symbolic fixed-target return laws

- Miguel Abadi and Benoit Saussol, *Hitting and returning into rare events for
  all alpha-mixing processes*.
- Version: arXiv:1003.4856v2, 31 May 2010.
- URLs: <https://arxiv.org/abs/1003.4856v2> and
  <https://arxiv.org/pdf/1003.4856v2>.
- Journal DOI: <https://doi.org/10.1016/j.spa.2010.11.001>.
- File: `abadi-saussol-1003.4856v2.pdf`.
- SHA-256: `f4a0ccfef0ba4db3bf947c9b4d5125f6b577d5a3b92d3eb9e6350f3b92dfe0fb`.
- Stable tuple: `arXiv:1003.4856v2|Theorem1;Example2;Proposition6;Theorem7`.
- Exact locators: shift/cylinder and alpha-mixing definitions, PDF pp. 2--3;
  Theorem 1, PDF p. 3; fixed target cylinder Example 2, PDF pp. 3--4;
  Proposition 6, PDF pp. 4--5; explicit hitting bound, Theorem 7, PDF p. 5.
- Scope: Example 2 permits a target cylinder centered at every fixed symbolic
  sequence, including periodic ones, but the starting trajectory remains
  random under the invariant measure. This is not a theorem about the orbit of
  the cylinder center or any other prescribed point.

## S4: short structured exponential sums

- Bryce Kerr, Laszlo Merai, and Igor E. Shparlinski, *On digits of Mersenne
  numbers*.
- Version: arXiv:2001.03380v4, 15 July 2021.
- URLs: <https://arxiv.org/abs/2001.03380v4> and
  <https://arxiv.org/pdf/2001.03380v4>.
- Journal DOI: <https://doi.org/10.4171/RMI/1316>.
- File: `kerr-merai-shparlinski-2001.03380v4.pdf`.
- SHA-256: `a4eaf55ed902d9925418a36f50d8851a5dba58c10520c2324607aefabddb134f`.
- Stable tuple: `arXiv:2001.03380v4|Theorem1.1;Corollary1.2;Theorem1.3;equations(3.9)-(3.11)`.
- Exact locators: Theorem 1.1 and equations (1.2)--(1.3), PDF p. 3;
  nontrivial range immediately after Theorem 1.1 and Corollary 1.2, PDF p. 3;
  block-frequency Theorem 1.3, PDF p. 4; interval and Erdos--Turan conversion,
  equations (3.9)--(3.11), PDF pp. 26--27.
- Scope: fixed odd prime base `q`, averages over primes `p<=X` and the numbers
  `2^p-1`, with nontrivial sum range
  `q^(gamma^(2/3+epsilon))<=X<=q^(A*gamma)`. It is neither decimal base 10 nor
  consecutive shifts of one fixed point. Theorem 1.3's error is additive
  `o(pi(X))`; it is not stated as relative error uniformly for growing `s`.

## Retrieval record

All four arXiv PDFs were retrieved successfully from the versioned URLs on
2026-08-12. A fifth candidate, Lawler--Sokal (1988), was discovered and its DOI
metadata inspected, but the primary AMS PDF returned HTTP 403; it is not used,
not called literature-checked, and is not counted among the four inspected
primary PDFs. No source statement in T158 depends on it.
