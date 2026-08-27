# T136 primary-source pins

Audit date: 2026-08-10.

Exactly six primary PDFs were opened. Each is absent from the supplied semantic
memory through T133 by exact-title, author, arXiv-ID, and file-name search.
`REPORT.md` records deductions and applicability screens; this file records
source statements only.

## M1. Spectral theory of regular sequences

- Domain: Mahler or functional-equation constants.
- Source: Michael Coons, James Evans, and Neil Manibo, "Spectral Theory of
  Regular Sequences," *Documenta Mathematica* 27 (2022), 629--653.
- DOI: <https://doi.org/10.4171/DM/880>.
- PDF: <https://content.ems.press/assets/public/full-texts/serials/dm/27/8965811/online/10.4171-dm-880.pdf>.
- Local file: `coons-evans-manibo-10.4171-dm-880.pdf`.
- SHA-256: `4badf20c29df7d19695675f6aa677b7e609d763c926ff99f30123bfe29fcf034`.
- Locators and exact ranges:
  - printed p. 632, Definition 1: a primitive real-valued `k`-regular sequence
    is nonnegative, not eventually zero, has nonnegative digit matrices, and
    has positive matrix `B=sum_a B_a`;
  - printed p. 633, Theorem 1: for such a primitive sequence, the normalized
    pure-point measure vectors converge weakly to a common probability measure;
  - printed p. 636, Corollary 2, equation (10): for every integer frequency
    `t` and `n>=1`, the finite Fourier vectors satisfy the displayed exact
    matrix recursion;
  - printed pp. 643--644, Theorem 5: if `rho(B)` is uniquely dominant,
    `rho(B)>rho_*({B_0,...,B_(k-1)})`, and the fundamental-region sums are
    governed by `rho(B)`, the limit function `F_f` exists and is Holder for
    every `alpha<log_k(rho/rho_*)`; the paragraph following the proof explicitly
    warns that these assumptions alone do not guarantee that `F_f` is the
    distribution function of a measure.
- T136 use: hypotheses and conclusion ranges for negative card NEG-M.

## M2. Base-3/2 Thue--Morse frequencies

- Domain: Mahler or functional-equation constants.
- Source: Julien Cassaigne, Bastian Espinoza, Michel Rigo, and Manon
  Stipulanti, "Symbols Frequencies in the Thue--Morse Word in Base 3/2 and
  Related Conjectures," arXiv:2602.21895v1, 25 February 2026.
- Abstract: <https://arxiv.org/abs/2602.21895v1>.
- PDF: <https://arxiv.org/pdf/2602.21895v1>.
- DOI: <https://doi.org/10.48550/arXiv.2602.21895>.
- Local file: `cassaigne-et-al-2602.21895v1.pdf`.
- SHA-256: `c2b12d420883ea5d4b60f3e7c259b7423cf069e5421b7983daac6b6e7e2076d5`.
- Locators and exact ranges:
  - printed p. 21, Theorem 18: for every `n>=0`, symbol `c in {0,1}`, and
    residue `k in Z`, `C_n(c,k,N)/N -> 2^(-n-1)`;
  - printed pp. 22--24, Lemma 19: subsequential limiting profiles exist and
    obey the exact desubstitution recurrence (10);
  - printed p. 25, Proposition 20: every nonnegative profile family satisfying
    periodicity, the recurrence, and normalization is uniformly `2^(-n-1)`;
  - printed pp. 29--34, equations (20)--(24) and Lemmas 23--25: Fourier
    iteration on the 2-adics; the calculation on printed p. 34 gives
    `||zeta_2||_infty <= 20/27 < 1`.
- T136 use: hypotheses and conclusion ranges for negative card NEG-M.

## F1. Slow Fourier decay

- Domain: arithmetic or fractal Fourier decay.
- Source: Simon Baker and Amlan Banaji, "Self-Similar and Self-Conformal
  Measures with Slow Fourier Decay," arXiv:2602.05593v1, 5 February 2026.
- Abstract: <https://arxiv.org/abs/2602.05593v1>.
- PDF: <https://arxiv.org/pdf/2602.05593v1>.
- DOI: <https://doi.org/10.48550/arXiv.2602.05593>.
- Local file: `baker-banaji-2602.05593v1.pdf`.
- SHA-256: `74d6e8d0192de706c84ad745b8bb9ce478e9735e8891bdbda3a25a4aeb59504d`.
- Locators and exact ranges:
  - printed p. 4, Theorem 1.3: for the explicit Liouville translation
    `t=sum_(m>=1)1/(10 tetrated to 3m)`, the three-map ratio-`1/10`
    self-similar measure is Rajchman but its Fourier transform has the stated
    positive inverse-log-log lower envelope at tetrational frequencies;
  - printed p. 5, Theorem 1.7: there are a decreasing positive `psi` and
    `gamma in (0,1)` with divergent `Psi`, logarithmic growth limsup one, and
    `R(x,N;gamma,psi,10)=0` for every support point `x` and every `N`;
  - printed pp. 18--21, proof of Theorem 1.7 and equations (2.13)--(2.16):
    explicit blockwise construction of `psi` and the avoided target.
- T136 use: exact falsification boundary in negative card NEG-F.

## F2. Fourier decay from L2-flattening

- Domain: arithmetic or fractal Fourier decay.
- Source: Simon Baker, Osama Khalil, and Tuomas Sahlsten, "Fourier Decay from
  L2-Flattening," arXiv:2407.16699v3, 20 December 2024.
- Abstract: <https://arxiv.org/abs/2407.16699v3>.
- PDF: <https://arxiv.org/pdf/2407.16699v3>.
- DOI: <https://doi.org/10.48550/arXiv.2407.16699>.
- Local file: `baker-khalil-sahlsten-2407.16699v3.pdf`.
- SHA-256: `95f0cc2e23c1c46438b51a331dcc69922cff0c1a266d646e47e2e16c78b8b0a0`.
- Locators and exact ranges:
  - printed p. 3, Definition 1.1: uniform affine non-concentration at every
    point, scale `0<r<=1`, and affine hyperplane;
  - printed pp. 4--5, Theorem 1.5: an affinely irreducible self-similar IFS
    with two contractions having a Diophantine log-ratio gives
    polylogarithmic Fourier decay for every associated self-similar measure;
  - printed p. 4 immediately before Theorem 1.5: Diophantine means
    `|alpha-p/q|>=c/q^ell` for every rational `p/q`, for some `c>0`, `ell>2`.
- Attribution boundary: Theorem 1.3 on printed p. 3 is explicitly attributed
  there to another source. It is not counted as a new primary-source result in
  T136 and is not a load-bearing source claim.
- T136 use: exact failed hypotheses and range in negative card NEG-F.

## X1. Character sums with matrix powers

- Domain: short structured exponential sums.
- Source: Alina Ostafe, Igor E. Shparlinski, and Jose Felipe Voloch,
  "Equations and Character Sums with Matrix Powers, Kloosterman Sums over Small
  Subgroups, and Quantum Ergodicity," *International Mathematics Research
  Notices* 2023, no. 16, 14196--14238; online 18 August 2022.
- DOI: <https://doi.org/10.1093/imrn/rnac226>.
- Abstract: <https://arxiv.org/abs/2110.10941>.
- PDF: <https://arxiv.org/pdf/2110.10941>.
- Local file: `ostafe-shparlinski-voloch-2110.10941.pdf`.
- SHA-256: `4ecd0a303f6b0c93953a2df1bd011a59e88a281745dfe363865dd6ace562c934`.
- Locators and exact ranges:
  - arXiv PDF p. 6, equation (2.1) and Theorem 2.4: diagonalizable
    `A in GL(n,q)`, two displayed linear-independence hypotheses, matrix order
    `tau`, determinant order `t`, and the two bounds split at `tau=q^(n/2)`;
  - arXiv PDF p. 6, Remark 2.6: twisted sums are covered and standard
    completion gives incomplete sums with one additional `log q` factor;
  - arXiv PDF p. 21 onward, Section 6.1: proof of Theorem 2.4.
- T136 use: exact dimension-one specialization and logarithmic screen NEG-X.

## X2. Weil sums over small subgroups

- Domain: short structured exponential sums.
- Source: Alina Ostafe, Igor E. Shparlinski, and Jose Felipe Voloch, "Weil
  Sums over Small Subgroups," *Mathematical Proceedings of the Cambridge
  Philosophical Society* 176 (2024), no. 1, 39--53; online 15 August 2023.
- DOI: <https://doi.org/10.1017/S0305004123000415>.
- Abstract: <https://arxiv.org/abs/2211.07739>.
- PDF: <https://arxiv.org/pdf/2211.07739>.
- Local file: `ostafe-shparlinski-voloch-2211.07739.pdf`.
- SHA-256: `fca26a67b1028436d195e9e1ad0b1e94953d10aea54e492ce80d9569925f2753`.
- Locators and exact ranges:
  - arXiv PDF p. 4, equations (1.5)--(1.7): definition of
    `eta_d(epsilon)`, including `eta_1=eta_2=7*epsilon/27`;
  - arXiv PDF pp. 4--5, Theorem 1.1: prime `p`, polynomial degree `d>=1`,
    subgroup order `tau>=p^(3/7+epsilon)`, and complete sum bound
    `O(tau*p^(-eta_d(epsilon)))`;
  - arXiv PDF p. 15 onward, Section 4: proof of Theorem 1.1.
- T136 use: exact complete-subgroup and range failure in negative card NEG-X.

## Retrieval record

All six HTTPS retrievals succeeded. `pdftotext -layout` produced nonempty text
for every PDF; no OCR was needed. No mathematical conclusion relies on a
source that failed retrieval.
