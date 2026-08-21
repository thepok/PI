# T11 adversarial recheck

Use this checklist against `HFE_PI_APPLICABILITY_MATRIX.md` and
`SOURCE_MANIFEST.md`.

## Target integrity

- [ ] Recompute the canonical statement hash and obtain
  `e2b6c9375936a97fe6cdd10c3f014613267f3c491935b536c6ec016c5f501e43`.
- [ ] Recompute the accepted T10 file hash and obtain
  `45003707a7b30447c9dd9ed5843f8c899a7c7107814c99f9b7a7a9f4ab8bf4ff`.
- [ ] Compare matrix Section 1 literally with T10 lines 70-78 and 1085-1097.
- [ ] Confirm the order `forall A epsilon, exists nstar, forall n, exists N`.
- [ ] Confirm that `N` may depend on `A`, `epsilon`, and `n`, while one `N`
  must handle all `1<=h<=ceil(A*n)` at that fixed scale.

## Source statements

- [ ] Salem--Zygmund printed pp. 333 and 337 state the scalar and complex
  coefficient distribution results; do not rely on garbled OCR formulas.
- [ ] Rudnick--Zaharescu Theorems 1.1-1.2 say almost all `alpha`, not every
  `alpha`; Proposition 4.1 integrates variance over `alpha`.
- [ ] Zeilberger--Zudilin printed p. 407 defines irrationality measure using
  every extra positive exponent, and p. 418 gives the stated numerical bound.
- [ ] Follow staged `t28/T28-lacunary-sum-audit.md` and its primary PDFs before
  accepting the EG, Philipp, or Fukuyama transcriptions; verify the staged
  audit and evidence hashes in `SOURCE_MANIFEST.md`. Do not treat T11's short
  reuse rows as independent replacements for that accepted audit.
- [ ] Follow T2 before accepting the Bailey--Crandall base and hypothesis
  classification.

## Applicability traps

- [ ] No a.e. or positive-measure theorem is specialized to `x=pi`.
- [ ] No finite bad-set estimate is treated as excluding a named singleton.
- [ ] No theorem for each fixed `h` is called uniform in a growing frequency
  range without the finite-intersection and threshold argument.
- [ ] No pair-correlation limit at radius `s/N` is identified with T10's
  weighted energy at radius `10^(-n)`.
- [ ] No parameter-integrated mean square is evaluated at `pi`.
- [ ] No finite digit or finite exponential-sum computation is used as an
  eventual-`n` proof.
- [ ] The irrationality-measure row claims only that the direct termwise use
  misses HFE; it does not claim that no future method could use that theorem.
- [ ] The all-negative matrix is not described as evidence against HFE, C2,
  C1, or A1.

## Algebra checks

- [ ] Verify `sum_{h<=H}w(n,H,h) < 1+2H*10^(-n)` from the first branch of
  the minimum.
- [ ] Verify orthogonality in equation (2): for `h>=1`, the integer
  frequencies `h*10^j` are distinct.
- [ ] Verify the Markov bound and that the selected `N_n` makes its right side
  summable.
- [ ] Do not assume the HFE weights are monotone in `H`. Verify instead that
  `w(n,H,h)<=1/(pi*h)` and that the displayed `U(n,m,N,x)` dominates every
  cutoff with `A<=m`.
- [ ] Verify that countable intersection over positive integers `m` and
  positive rationals `rho` covers every real `A,epsilon>0`.
- [ ] Verify from `|pi-p/q|>q^(-nu)` that `||q*pi||>q^(1-nu)`.
- [ ] Restrict that implication to denominators `q>=Q_0(nu)`; omitted finite
  pairs are not silently assigned the asymptotic lower bound.
- [ ] Verify `1-cos(2*pi*d)>=8d^2` on `0<=d<=1/2`.
- [ ] Verify that `sum_j j*10^(-2*(nu-1)*j)` converges for `nu>mu0>1`.
- [ ] Interpret the convergent series only as the bounded subtraction
  certified by the direct argument, not as an upper bound on the true phase
  deficit.

## Scope conclusion

The only permitted conclusion is: no theorem in this bounded pinned matrix
establishes `HFE_pi`; the first gaps are recorded row by row. The artifact is
`literature-checked`, not a proof or disproof of the agenda's conjectures.
