# T164 source pins

Inspection date: 2026-08-12 UTC. PDFs are authoritative. Text files are
mechanical `pdftotext -layout` derivatives. No OCR was used.

## S1: finite return-word and derived-word machinery

- Fabien Durand, *A characterization of substitutive sequences using return
  words*, Discrete Mathematics 179 (1998), 89-101.
- URL: <https://arxiv.org/abs/0807.3322>; PDF:
  <https://arxiv.org/pdf/0807.3322>.
- Local PDF: `durand-0807.3322.pdf`; SHA-256
  `eb08490237dc821f54f9c54ba385f98d1abac69a4e03121f06955fb98329e40a`.
- Local text: `durand-0807.3322.txt`; SHA-256
  `17779341b757257b9dcca870db2240e837d730094358196455fab3ee15d407fa`.
- Stable tuple: `arXiv:0807.3322v1|Definition1-4;Proposition6;Lemma13;Theorem17-20`.
- Exact locators: substitution, primitive substitution, fixed point, and
  uniform recurrence definitions, displayed PDF pp. 3-4; return words and
  unique coding, Section 2.3 and Proposition 6, pp. 4-5; bounded iterate-length
  ratio, Lemma 13, p. 8; finite-power theorem with
  `N=4 r S(zeta) Q`, Theorem 17 and its proof, pp. 9-10; proportional lower
  and upper return lengths, Theorem 18, pp. 10-11; return substitution and
  finiteness of derivated sequences, Proposition 19 and Theorem 20, pp. 11-12.
- Scope used here: the identity projection of a one-sided fixed point of a
  primitive substitution. T164 makes every constant in Theorem 17 effective
  directly from the finite substitution; it does not import a numerical
  constant from this source.

## S2: linearly recurrent return bounds

- Fabien Durand, *Linearly recurrent subshifts have a finite number of
  non-periodic subshift factors*, Ergodic Theory and Dynamical Systems 20
  (2000), 1061-1078.
- URL: <https://arxiv.org/abs/0807.4430>; PDF:
  <https://arxiv.org/pdf/0807.4430>.
- Local PDF: `durand-0807.4430.pdf`; SHA-256
  `627b56882a2a6235fab08f62c8365a4c08c4e91602f6a522b40a54aa4d46e043`.
- Local text: `durand-0807.4430.txt`; SHA-256
  `7015f9f21d2ef86dc5fbfb13e23f7137f9805f17d32c504a1ce2a8c4c147ae58`.
- Stable tuple: `arXiv:0807.4430v1|Definition2;Proposition5;Section2.6;Proposition6`.
- Exact locators: return words and linear recurrence, Definition 2, displayed
  PDF p. 5; lower return bound and power-freeness for an aperiodic linearly
  recurrent subshift, Proposition 5(3)-(4), p. 6; primitive substitution
  subshifts are linearly recurrent, Section 2.6, p. 7; constructive constants
  in the primitive S-adic proof, Proposition 6 and Lemmas 7-8, pp. 8-9.
- Scope used here: confirmation that return-word lower separation is the
  source-native invariant. T164's certificate uses the sharper explicit
  finite-power constant reconstructed from S1, so no unspecified LR constant
  is used.

## S3: decidability and critical-exponent boundary

- Dalia Krieger, *Critical Exponents and Stabilizers of Infinite Words*, PhD
  thesis, University of Waterloo, 2008.
- Repository landing page:
  <https://uwspace.uwaterloo.ca/items/e0f8311e-afc3-46eb-92f3-69af230e8340>.
- Download URL:
  <https://uwspace.uwaterloo.ca/bitstreams/3eb22b0d-c1e0-4d21-91f7-80a483e528b4/download>.
- Local PDF: `krieger-thesis-2008.pdf`; SHA-256
  `165846416cf3d485725edd0f302603d6cda8d8f3a977d84cc155d516bc657e22`.
- Local text: `krieger-thesis-2008.txt`; SHA-256
  `448534ac1f60756234d377c26e2bc22b94fcc492f391c0403f5460aa1b05284f`.
- Stable tuple: `Krieger-thesis-2008|Definition2.2;Section3.2.1;Section5.2;Section6.4;Section6.5.1`.
- Exact locators: period and fractional-power definitions, printed pp. 10-13;
  primitive substitutions and fixed points, pp. 13-16; Mossé's bounded-power
  result and decidability of repetitiveness, Section 3.2.1, pp. 25-29;
  Thue-Morse critical exponent `2`, Example 5.4, printed p. 65; general
  computation boundary and explicit statement that boundedness is decidable,
  Section 6.4, printed pp. 126-127, especially Notes 1 and 3; Fibonacci
  critical exponent `2+tau`, Section 6.5.1, printed pp. 128-130.
- Scope used here: decidability of whether the D0L fixed point has finite
  critical exponent. The thesis explicitly says exact critical-exponent
  computation has additional problems; T164 does not claim that stronger
  computation. It needs only the finite/infinite decision.

## Reused T162 boundary

The accepted T162 literature package is changed evidence, not a premise.
T162 identified minimum return separation as the order-sensitive candidate
and observed that maximum return length does not lower-bound it. T164 neither
imports T162's prose deductions nor treats them as proved. It proves the lower
bound independently through finite power-freeness and uses S1-S3 above.
