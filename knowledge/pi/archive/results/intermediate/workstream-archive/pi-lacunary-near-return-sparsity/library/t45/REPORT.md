# T45: deterministic mixed-lacunary estimate audit

Audit date: 2026-08-01 UTC

Claim labels:

- `literature-checked` for the literal statements and applicability verdicts in
  the bounded four-source corpus below.
- `proof sketch` for the finite aggregate primitive-class regrouping quoted
  from and rechecked against the T43 note. T43 is an unverified note, not a
  discharged premise.

Terminal verdict: **DOES NOT APPLY** for every retained theorem. No retained
theorem supplies a positive lower bound at the genuine fixed-`pi` T26
coefficient over all of the required T38 variables. This is a bounded-corpus
finding, not a claim that no such theorem exists.

## 1. Immutable statement and quantifiers

The byte-identical file `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

It defines the ordered, diagonal-inclusive count

\[
 Q_\pi(n,N)=\#\{(i,j)\in\{0,\ldots,N-1\}^2:
 \|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}\}
\]

and asks whether

\[
 \forall A\in\mathbb N_{\geq1}\ \exists n_0\geq1\
 \forall n\geq n_0\ \exists N\geq1:
 \qquad AnQ_\pi(n,N)\leq N^2.                    \tag{1.1}
\]

`N` may depend on `A,n`. This audit does not replace eventual `n` by
infinitely many `n`, prescribe `N`, delete diagonal pairs, change strict circle
distance, replace base 10, or replace `pi` by an almost-everywhere multiplier.
It proves neither (1.1) nor its negation.

### Interpretation issues fixed before the audit

1. T43 is a `proof sketch`. Its aggregate primitive-correlation (APC)
   identity is tested as the stated target, not cited as a proved consequence.
2. "Fixed point" means the coefficient returned by T26. A theorem that
   integrates over a free multiplier, proves an almost-everywhere statement,
   or chooses a favorable point does not certify that coefficient.
3. "Uniform" means that every theorem constant and cutoff needed in the
   application is valid independently of the genuine chain parameters and of
   every legal `ell` and `R`; a constant deteriorating with `R` does not give a
   uniform T38 bridge.
4. "Mixed" means the complete weighted `(u,j)` family. A theorem for each
   fixed `u` separately is recorded as partial spectral coverage, not as an
   aggregate estimate.
5. T38's FSFS is a local conditional predicate. Even a local analytic bound
   must not be reported as uniform adjacent compatibility or canonical (1.1)
   without all later selection hypotheses.
6. The T43 note does not formalize which global existential or uniform
   selection quantifiers would suffice beyond one local APC instance. This
   audit therefore checks theorem uniformity on all genuine local ranges and
   makes no global selection claim.

## 2. Genuine T26/T38 target

The exact vendored kernel-checked inputs are:

| Input | SHA-256 | Locators used |
|---|---|---|
| `T26SharedResonanceChain.lean` | `7278999f1ff89d11e7ee408b21e5a300fbdc3e78cf5a6776a2274fc9a761f1c2` | geometric chain and coefficient, lines 125-173; literal failure parameters, lines 285-311 and 365-395 |
| `T38FixedStratumFejerSpike.lean` | `853f10a83b0dbf91955f7587c07cd4651e5954b19f78942703df15073456a014` | stratum, lines 34-105; radius, order, and FSFS, lines 329-411; expansion, lines 622-718 |

The T26 files are machine-checked. The following is a literal unpacking of
their displayed definitions and theorem types, not an invocation of T43.
Under the temporary hypothesis that (1.1) fails, T26 returns `A>=1`; for
arbitrarily large `n>=1` and each requested depth `d`, it uses

\[
 D_0=131072A^2n^2,\qquad
 K=2\,\operatorname{densityDenominator}(D_0,d)^2,             \tag{2.1}
\]

\[
 L=\operatorname{iterationLengthThresholdAux}(D_0,1,K,1,d),
 \qquad N=16AnL.                                             \tag{2.2}
\]

It supplies

\[
 1\leq r\leq N-1,\qquad 1\leq h\leq256An,                  \tag{2.3}
\]

and one list of `d` distinct shifts `s_t`, each at least 1 and different from
`r`. At node `q<=d`, define

\[
 M_q=N-r-\sum_{t<q}s_t,\qquad
 D_q=\operatorname{densityDenominator}(D_0,q),               \tag{2.4}
\]

\[
 \boxed{\beta_q=h(10^r-1)\pi\prod_{t<q}(10^{s_t}-1)}.       \tag{2.5}
\]

The coefficient is not free. T26 retains

\[
 \frac{M_q}{D_q}<\left|\sum_{x=0}^{M_q-1}e(\beta_q10^x)\right|.
                                                                    \tag{2.6}
\]

For one consecutive pair `q,q+1`, T38 takes `k : Fin d`, a legal stratum

\[
 1\leq D_0,\qquad 1\leq\ell<
 \min\{M_q,M_{q+1}\},                                      \tag{2.7}
\]

and the adjacent multiplier `U=10^(s_q)-1`. Its exact radius and order are

\[
 \delta=\min\left\{\operatorname{inverseError}(\tau_q),
 \frac{\operatorname{inverseError}(\tau_{q+1})}{U},
 \frac1{2U10^\ell}\right\}>0,
 \qquad R=\lceil\delta^{-1}\rceil,                         \tag{2.8}
\]

where `tau_q=1/(8D_q^2)`. The vendored T38 lemma gives `U>=1`; thus legal
`ell>=1` implies `delta<=1/20` and `R>=20`. The T43 note further argues from
the genuine shift formula that `U>=9` and hence `R>=180`. Every negative
verdict below already holds for all `R>=20`, so it covers both the
kernel-visible T38 range and T43's narrower claimed range without taking the
unverified `R>=180` deduction as a premise.

For `0<=j<ell`, put

\[
 Q_j=10^\ell-10^j.                                         \tag{2.9}
\]

T38's kernel-checked expansion has signed cutoff and weights

\[
 |u|\leq R-1,\qquad w_R(u)=1-\frac{|u|}{R},                \tag{2.10}
\]

and gives

\[
 E_{\ell,R}(\beta_q)
 =\sum_{|u|\leq R-1}w_R(u)\sum_{j<\ell}
   e\bigl(\beta_q uQ_j\bigr).                              \tag{2.11}
\]

The analytic part of FSFS is the strict pointwise lower bound

\[
 \boxed{E_{\ell,R}(\beta_q)>
 \frac{\ell}{4R\delta^2}.}                                 \tag{2.12}
\]

Pairing signs in the finite sum (2.11), and uniquely writing every positive
`u<R` as `u=10^a m` with `10` not dividing `m`, gives the finite identity

\[
 E_{\ell,R}(\beta)=\ell+2
 \sum_{\substack{1\leq m<R\\10\nmid m}}
 \sum_{\substack{a\geq0\\10^am<R}}
 \left(1-\frac{10^am}{R}\right)
 \sum_{j<\ell}\cos(2\pi\beta10^amQ_j).                    \tag{2.13}
\]

This elementary regrouping is the part presently at `proof sketch` level.
Substitution into (2.12) yields T43's exact local APC target

\[
 \boxed{
 \sum_{\substack{1\leq m<R\\10\nmid m}}
 \sum_{\substack{a\geq0\\10^am<R}}
 \left(1-\frac{10^am}{R}\right)
 \sum_{j<\ell}\cos(2\pi\beta_q10^amQ_j)
 >\frac{\ell}{8R\delta^2}-\frac\ell2.}                    \tag{APC}
\]

No average over `beta`, no replacement coefficient, and no post hoc choice of
`beta` is permitted.

## 3. Bounded search and source pins

The stopping rule was fixed to four theorem families named by the agenda:
one deterministic large-sieve theorem, one mixed lacunary-spectrum theorem,
one Riesz-product/Sidon characterization, and one genuine multilinear
dissociated-set inequality. Search results were capped at 20 records per query.
Queries included `lacunary exponential sum large sieve`, `lacunary
Khintchine`, `Riesz products Sidon`, `dissociated Rudin inequality`, and
`multilinear lacunary correlation`, followed by exact-title checks in arXiv,
Crossref, NUMDAM, and Centre Mersenne.

T3 was checked first. None of its six sources is retained here: Rudnick and
Zaharescu 1999/2002, Philipp 1967, Yesha 2023, Li-Liao-Velani-Zorin 2023, and
Yuan-Wang 2024. No old T3 theorem is relabeled as a new mixed theorem.

| ID | Primary source and retrieval URL | PDF SHA-256 | Exact theorem locator |
|---|---|---|---|
| BD69 | E. Bombieri and H. Davenport, *Some inequalities involving trigonometrical polynomials*, Ann. Scuola Norm. Sup. Pisa 23 (1969), 223-241. [NUMDAM record](https://www.numdam.org/item/ASNSP_1969_3_23_2_223_0/), [PDF](https://www.numdam.org/item/ASNSP_1969_3_23_2_223_0.pdf) | `a3bcb2b05c9b4807c6b502ad73ce50e6c7423e88ad00974facf9759d71772c74` | definitions (1)-(2), journal p. 223; Theorem 1 and (4), p. 224 |
| B70 | A. Bonami, *Etude des coefficients de Fourier des fonctions de Lp(G)*, Ann. Inst. Fourier 20(2) (1970), 335-402. [DOI](https://doi.org/10.5802/aif.357), [PDF](https://aif.centre-mersenne.org/item/10.5802/aif.357.pdf) | `921508d99be0186f5fa5ab177d59003522bf4e477ac8a8c2c267c406445ce0fb` | definition of `A(q,E)`, pp. 340-341, text lines 180-215; Corollary 4, p. 361, lines 1097-1114 |
| B85 | J. Bourgain, *Sidon sets and Riesz products*, Ann. Inst. Fourier 35(1) (1985), 137-148. [DOI](https://doi.org/10.5802/aif.1003), [PDF](https://aif.centre-mersenne.org/item/10.5802/aif.1003.pdf) | `cffd6d6ec3b0d6ad0344a1e2a55cbf5cc2dd2290c685846627292ca87543d8c3` | Sidon and Riesz-product definitions, pp. 137-138, lines 42-82; main theorem, pp. 138-139, lines 102-125 |
| S10 | I. D. Shkredov, *Some applications of W. Rudin's inequality to problems of combinatorial number theory*, arXiv:1002.1886v1 (2010). [record](https://arxiv.org/abs/1002.1886v1), [PDF](https://arxiv.org/pdf/1002.1886v1) | `dabdfa4ecac63c33892859653f1436fadaa5cd400828bb09a36de2f997eaf77d` | dissociation and Theorem 1.1, preprint p. 1, lines 20-39; Theorem 1.4, p. 2, lines 79-90; Theorem 3.7, p. 12, lines 723-740 |

All text derivatives were made with `pdftotext -layout`. Their hashes are in
`SHA256SUMS`. BD69 is an image scan and its text derivative drops displayed
mathematics. The exact definitions and inequality were therefore checked
visually against the included 300 dpi renders
`bombieri-davenport-1969-p223.png` and
`bombieri-davenport-1969-p224.png`, hashes
`983cfabd247ca70622e776c15dd877174c25f52e07e421744f8031e176b9d35c`
and `c602d8d50c49a85e6a101976bc38d8021a4a1f4aa4c57eee9fe1ce4afa732225`.
OCR could not be generated because `tesseract` is absent in the sandbox; no
approximate OCR text is presented as an exact quote.

Two candidates were excluded after retrieval failure: the Wiley PDF for
Montgomery-Vaughan's *The large sieve* returned HTTP 403, and the IUMJ source
for Rudin's *Trigonometric Series with Gaps* failed TLS verification. These
failures reinforce that the corpus is bounded, not exhaustive.

## 4. BD69: deterministic large sieve

### Literal theorem

Let `B` be a positive integer, let `a_(M+1),...,a_(M+B)` be arbitrary real or
complex numbers, and define

\[
 S(x)=\sum_{n=M+1}^{M+B}a_ne(nx).
\]

Let `x_1,...,x_J` be real numbers satisfying
`||x_r-x_s||>=Delta` for `r!=s`, where `0<Delta<=1/2`. Theorem 1 states that
if `B Delta>=1`, then

\[
 \sum_{r=1}^J|S(x_r)|^2
 <B\left(1+\frac5{B\Delta}\right)
 \sum_{n=M+1}^{M+B}|a_n|^2.                                \tag{4.1}
\]

This transcription was visually checked against pp. 223-224 and equations
(1), (2), and (4) in the pinned render.

### Exact substitution and verdict

Group equal integer frequencies in (2.11). The resulting coefficients `c_v`
are arbitrary complex coefficients supported in the consecutive interval

\[
 -W\leq v\leq W,\qquad W=(R-1)(10^\ell-1).                 \tag{4.2}
\]

Zero-filling gives `B_spec=2W+1` consecutive coefficients. Set `J=1`,
`x_1=beta_q`, and `Delta=1/2`. Separation is vacuous. On the genuine T38
range `ell>=1`, `R>=20`, one has `W>0`, hence `B_spec>=3` and
`B_spec Delta>=1`. Thus BD69 literally permits the genuine fixed point and
gives

\[
 |E_{\ell,R}(\beta_q)|^2
 <(B_{\rm spec}+10)\sum_{v=-W}^W|c_v|^2.                  \tag{4.3}
\]

- Coefficient domain: permits all grouped T38 coefficients.
- Cutoffs: permits every genuine T38 `ell,R`, but pays the full spectral
  diameter `B_spec`, of order `R 10^ell`; the theorem's hypothesis excludes
  the irrelevant degenerate band `B_spec=1` at `Delta=1/2`.
- Scope: deterministic and fixed-point; not almost everywhere.
- First preventing component: conclusion direction. Equation (4.3) is an
  upper magnitude bound, while APC is a positive pointwise lower bound.
- Verdict: **DOES NOT APPLY**.

The theorem is not reported as fixed-`pi` evidence merely because `J=1`
allows `beta_q`: its conclusion cannot imply APC.

## 5. B70: mixed lacunary spectra

### Literal theorem

Bonami defines `A(q,E)` for `q>2` as the least constant such that every
trigonometric polynomial `f` with spectrum in `E` satisfies

\[
 \|f\|_{L^q(\mathbb T)}\leq A(q,E)\|f\|_{L^2(\mathbb T)}.  \tag{5.1}
\]

Corollary 4 states: if `(lambda_n)` is a sequence of integers with
`lambda_(n+1)>=2 lambda_n`, and `E_k` is the set of integers representable as

\[
 \pm\lambda_{n_1}\pm\cdots\pm\lambda_{n_k},
 \qquad n_1>\cdots>n_k,                                    \tag{5.2}
\]

then `E_k` is `A(q)` for every `q` and there is a constant `A(k)` such that

\[
 A(q,E_k)\leq A(k)q^{k/2}.                                 \tag{5.3}
\]

The quantification over polynomials allows arbitrary finite complex Fourier
coefficients on `E_k`.

### Exact substitution and verdict

For each fixed positive `u`, take `lambda_n=u10^n` and `k=2`. Then every

\[
 uQ_j=u10^\ell-u10^j\quad(0\leq j<\ell)                   \tag{5.4}
\]

belongs to `E_2`. Equations (5.1)-(5.3) therefore give an `L^q(d beta)` upper
bound for each fixed-`u` inner polynomial, with a constant independent of
`u,ell`.

- Coefficient domain: arbitrary coefficients for each fixed-`u` block.
- Cutoffs: uniform in `u,ell`; no single application covers all `1<=u<R`
  with their Fejer weights and cross-`u` collisions.
- Scope: Haar `L^q` over a free `beta`, not a value at `beta_q`.
- First preventing hypothesis: fixed-point scope. No theorem premise or
  conclusion identifies `beta_q` as a point satisfying a lower bound.
- Verdict: **DOES NOT APPLY**.

This is genuine mixed two-lacunary average control, but it is not fixed-`pi`
evidence and does not survive aggregation by simply summing upper norms.

## 6. B85: Sidon sets and Riesz products

### Literal theorem

For a compact abelian group `G` with dual `Gamma`, Bourgain calls
`Lambda subset Gamma` Sidon if one constant `C` satisfies

\[
 \sum_{\gamma\in\Lambda}|c_\gamma|
 \leq C\left\|\sum_{\gamma\in\Lambda}c_\gamma\gamma
 \right\|_\infty                                            \tag{6.1}
\]

for every finitely supported scalar family. A set is quasi-independent if
every relation with coefficients in `{-1,0,1}` is trivial. For a
quasi-independent finite set `A`, the paper defines the positive Riesz product

\[
 \prod_{\gamma\in A}(1+\operatorname{Re}(a_\gamma\gamma)),
 \qquad |a_\gamma|<1.                                      \tag{6.2}
\]

The main theorem states that the following are equivalent for `Lambda`:

1. `Lambda` is Sidon.
2. For every finite scalar family and every `p>1`,
   \[
   \left\|\sum c_\gamma\gamma\right\|_{L^p(G)}
   \leq C\sqrt p\left(\sum|c_\gamma|^2\right)^{1/2}.
   \]
3. There is `delta>0` such that every finite `A subset Lambda` contains a
   quasi-independent `B` with `|B|>delta|A|`.
4. There is `delta>0` such that every finite scalar family has a
   quasi-independent support subset carrying more than a `delta` fraction of
   its `l^1` mass.

### Exact support test and verdict

For any fixed `j`, the positive T38 support contains

\[
 Q_j\{1,2,\ldots,R-1\}.                                    \tag{6.3}
\]

If a subset `B` of `{1,...,R-1}` is quasi-independent and `|B|=b`, all `2^b`
subset sums are distinct and lie in `[0,b(R-1)]`. Hence

\[
 2^b\leq b(R-1)+1.                                         \tag{6.4}
\]

No `delta>0` independent of `R` can make `b>delta(R-1)` satisfy (6.4) for
unbounded `R`. Thus the full T38 ranges do not supply Bourgain's uniform
proportional quasi-independence, equivalently a uniform Sidon constant.

- Coefficient domain: arbitrary finite scalars if a Sidon set is supplied.
- Cutoffs: every individual finite support is Sidon with a support-dependent
  constant, but no source constant is uniform as genuine `R` grows.
- Scope: the norm statement is Haar `L^p`; the Riesz-product interpolation
  averages products and does not evaluate the prescribed `beta_q`.
- First preventing hypothesis: uniform Sidon/quasi-independence fails on the
  exact full `u` cutoff (6.3).
- Verdict: **DOES NOT APPLY**.

Even a tuple-dependent Sidon estimate would remain an upper norm estimate and
could select a favorable point different from `beta_q`.

## 7. S10: multilinear dissociated-set inequality

### Literal theorem

For a finite abelian group, Shkredov defines `Lambda` to be dissociated if

\[
 \sum_{\lambda\in\Lambda}\varepsilon_\lambda\lambda=0,
 \quad\varepsilon_\lambda\in\{0,\pm1\}
 \quad\Longrightarrow\quad
 \varepsilon_\lambda=0\text{ for all }\lambda.             \tag{7.1}
\]

Theorem 1.4 quantifies over every finite abelian group `G`, every integer
`l>=2`, every dissociated `Lambda`, and arbitrary subsets
`S_1,...,S_l subset G`. With `N=|G|`, it gives an absolute `C_3>0` and an
upper bound of the form

\[
 \sum_{x\in\Lambda}(1_{S_1}*\cdots*1_{S_l})(x)^2
 \leq C_3\frac{|S_l|}{N}
 \left(\sum_{\xi\in\widehat G}
 \prod_{j=1}^{l-1}|\widehat{1_{S_j}}(\xi)|^2\right)\log N.
                                                                    \tag{7.2}
\]

Theorem 3.7, formula (39), records the slightly stronger version used to
derive it. The coefficients in (7.2) come from indicator-set convolutions;
they are not arbitrary Fejer coefficients.

### Exact support test and verdict

Every legal T38 tuple has `R>=20`. For every fixed `j`, its positive support
therefore contains the three distinct integer frequencies

\[
 Q_j,\quad2Q_j,\quad3Q_j,
 \qquad Q_j+2Q_j-3Q_j=0.                                  \tag{7.3}
\]

Thus the exact full support is not dissociated. Reduction modulo a sufficiently
large cyclic group preserves (7.3), so passing to a finite group cannot repair
the first hypothesis.

- Coefficient domain: indicator convolutions, not arbitrary Fejer weights.
- Cutoffs: the dissociation failure occurs already at `R=4`, uniformly before
  either the T38 lower range `R>=20` or T43's claimed `R>=180`.
- Scope: a global finite-group upper correlation bound, not pointwise
  evaluation at one character.
- First preventing hypothesis: the exact T38 frequency support is not
  dissociated, by (7.3).
- Verdict: **DOES NOT APPLY**.

This is a genuinely multilinear theorem, but it supplies neither the required
frequency hypothesis nor the direction and coefficient domain of APC.

## 8. Applicability matrix

| Source | Literal coefficient domain | Cutoff and parameter uniformity | Scope | First failed requirement | Verdict |
|---|---|---|---|---|---|
| BD69, Thm. 1 | arbitrary finite real/complex coefficients in one consecutive band | every genuine T38 band (`ell>=1`, `R>=20`); cost is full width `2(R-1)(10^ell-1)+1` | deterministic separated sample points; `J=1` permits fixed `beta_q` | gives an upper square bound, not APC's positive lower bound | **DOES NOT APPLY** |
| B70, Cor. 4 | arbitrary polynomial coefficients on fixed `E_2` | uniform for each fixed `u`; not the complete cross-`u` aggregate | Haar `L^q(d beta)` | no value or lower bound at prescribed `beta_q` | **DOES NOT APPLY** |
| B85, main theorem | arbitrary finite scalars conditional on Sidon support | no Sidon/quasi-independent constant uniform in unbounded `R` | Haar `L^p`, supremum, and averaged Riesz products | full T38 support fails uniform proportional quasi-independence | **DOES NOT APPLY** |
| S10, Thm. 1.4/3.7 | indicator-set convolutions | all finite groups and `l>=2`, conditional on dissociated support | global finite-group upper correlation | exact support has `Q_j+2Q_j-3Q_j=0` | **DOES NOT APPLY** |

No theorem is classified `APPLIES` or `CONDITIONAL`: BD69 applies as a formal
upper bound but not to the target conclusion; the other three fail an actual
scope or support hypothesis before any fixed-`pi` conclusion can be drawn.

Almost-everywhere statements are not retained. Haar norm estimates are
reported only as norm estimates, not as evidence at `pi`. No synthetic
coefficient is used as evidence.

## 9. First missing hypothesis and one formalization target

The bounded corpus leaves one genuinely fixed-point hypothesis:

> At the prescribed coefficient (2.5), for at least the local chain/stratum
> selection actually required downstream, the complete Fejer-weighted mixed
> `(u,j)` sum must satisfy the strict APC lower bound, with constants uniform
> over the genuine T26/T38 parameter ranges.

T26's one-node resonance (2.6) does not supply sign control for this mixed
family. The audited average and structural theorems do not convert it into
such control.

The sole proposed formalization target is the finite identity and equivalence

```text
For every real beta and natural ell,R with 1 <= R,
the real part of T38.lacunaryExpansion beta ell R equals the
right side of (2.13); consequently T38's analytic strict inequality
is equivalent to APC with threshold ell/(8*R*delta^2)-ell/2.
```

This target would make the literature-audit interface machine-checkable. It
would not prove APC at `pi`, FSFS, adjacent compatibility, canonical (1.1), or
canonical C1.

## 10. Reproduction

From a directory containing only these delivered artifacts, run

```bash
python3 verify_audit.py
```

The verifier checks every pinned hash, canonical and Lean dependency pins,
text locator anchors, report verdict coverage, PDF/PNG signatures, and the
manifest. BD69's exact displayed formulas must additionally be inspected in
the two pinned PNG renders because the scan defeats text extraction.

Final conclusion: **bounded literature audit DOES NOT APPLY**. The result is
negative but informative: none of the retained deterministic large-sieve,
mixed lacunary, Riesz-product, or multilinear estimates provides the missing
fixed-`pi` APC lower bound. No FSFS, compatibility, canonical C1, or canonical
A1 claim is made.
