# Ramanujan fivefold defect: normalized arithmetic

Date: 2026-09-06. Claim labels: `conjecture`, `experiment`, `proof sketch`,
`literature-checked` as separated below. No Lean formalization or novelty claim.
This is an intermediate arithmetic investigation, **not an admitted digit
candidate** and not a reopening of the closed direct carry-killing route.

An [exact Frobenius comparison proof sketch](20260906-ramanujan-frobenius-proof-sketch.md)
now supplies exact vanishing of the three remainder constants and the
all-cutoff regularity below. Its rational identities passed independent
reproduction; an independent Pro review found no blocking error and supplied
explicit global-comparison completions, now incorporated with primary-source
checks. The status is a reviewed `proof sketch`, not a `verified resolution`
or Lean `machine-checked` result. The earlier finite-precision argument is
retained below, with its own strictly weaker scope.

A separate Fable5.1 review of the earlier partial-result version found no
blocking error in the interpolation, truncation estimates, bounded completion
or uniform valuation-loss calculation. That review did not read the later
exact Frobenius comparison; its older unresolved-remainder scope is not an
additional review of the all-cutoff proof.

## Exact object and the initial conjecture

Put
\[
b_N=\binom{2N}{N}^3/256^N,\qquad
S_N=\sum_{j=0}^{N-1}(6j+1)b_j,\qquad D_N=S_{5N}-5S_N,
\]
and, for every integer \(N\ge1\),
\[
U_N=\frac{D_N}{125N^3b_N}.
\]
The distinguished real identity is \(S_\infty=4/\pi\).

The initial `conjecture`, now supported by the linked reviewed `proof sketch`,
is that there is a 1-Lipschitz function \(V:\mathbb Z_5\to\mathbb Z_5\)
with \(U_N=12+25V(N)\). Equivalently,
\[
U_N\in12+25\mathbb Z_5,\qquad
v_5(U_M-U_N)\ge2+v_5(M-N)\quad(M\ne N).
\]
No cutoff is excluded. In particular the assertion includes arbitrarily large
valuation losses from \(N\) and \(\binom{2N}{N}\). Its first part would imply
\[
v_5(D_N)=3+3v_5(N)+3v_5\!\binom{2N}{N}.
\]
Neither this valuation law nor the global regularity follows from the
finite experiments. The linked exact-comparison argument supplies a
`proof sketch` of both, in the stronger restricted-analytic form.

## Literature boundary

`literature-checked`: Sun's **2019 edition** of *Open Conjectures on Congruences*,
Conjecture 22(i), equation (2.15), already conjectures, for every prime \(p>3\)
and positive integer \(n\),
\[
\frac{256^{n-1}}{(pn)^3\binom{2n-1}{n-1}^3}
\bigl(S_{pn}-(-1)^{(p-1)/2}pS_n\bigr)\equiv-E_{p-3}\pmod p.
\]
At \(p=5\), its left side is \(U_n/32\), hence it conjectures
\(U_n\equiv2\pmod5\), including nonunit cutoffs. This weaker assertion is
**not ours**. The stronger modulo-25 and Lipschitz assertions above have not
been established as novel; the subsequent-literature check remains open.
The older arXiv:0911.5665 edition has different numbering.

Primary sources:

- [Sun, author-uploaded 2019 text, Conjecture 22 and (2.15)](https://www.researchgate.net/publication/336577970_Open_Conjectures_on_Congruences).
- [Mao–Wen, arXiv:1910.00779, Theorem 1.1](https://arxiv.org/abs/1910.00779): full prime-length sum modulo \(p^4\); not the arbitrary-cutoff statement.
- [Mao–Sun, arXiv:2109.09877, Theorem 1.1 and introduction](https://arxiv.org/html/2109.09877v1): half prime-length sum modulo \(p^5\), a different truncation.

## Exact recurrence and an absolute first layer

`proof sketch`. Define \(P_5(m)=\prod_{1\le j\le m,\,5\nmid j}j\),
\[
G(N)=\frac{P_5(10N)}{P_5(5N)^2},\qquad
H(N)=G(N)^3\,256^{-4N}=\frac{b_{5N}}{b_N},
\]
\[
B(N)=\sum_{a=0}^4(30N+6a+1)
 \prod_{j=0}^{a-1}\frac{(10N+2j+1)^3}{32(5N+j+1)^3}.
\]
All denominators in \(B\) are units modulo 5. The coefficient ratio
\(b_{m+1}/b_m=(2m+1)^3/[32(m+1)^3]\) gives exactly
\[
D_{N+1}-D_N=b_N\{H(N)B(N)-5(6N+1)\}.
\]
For \(N\ge1\), this is
\[
125\left[\frac{(2N+1)^3}{32}U_{N+1}-N^3U_N\right]
=H(N)B(N)-5(6N+1).
\]
Forward division is singular at \(N\equiv2\pmod5\), backward division at
\(N\equiv0\pmod5\). Regular coefficients alone do not establish regularity
of the solution determined by the partial sums.

A weaker absolute congruence does hold by an elementary telescoping calculation:
\[
\boxed{D_N\equiv250N^3b_N\pmod{625}\quad(N\ge0).}
\]
Here congruences are in the localization of \(\mathbb Z\) at 5. To check it,
\[
\frac{\prod_{a=1}^4(5j+a)}{24}
\equiv1+125\left(\frac j{12}+\frac{7j^2}{24}\right)\pmod{625}
\]
gives \(G(N)\equiv1+125N^3\pmod{625}\). Since
\(256^{-4}\equiv481\pmod{625}\), binomial expansion gives
\[
H(N)\equiv1+530N+450N^2+500N^3\pmod{625}.
\]
Expanding the five rational terms gives
\[
B(N)\equiv130+5N+350N^2+500N^3\pmod{625}.
\]
Their product minus \(5(6N+1)\) is congruent to
\(250[(2N+1)^3/32-N^3]\). Multiplication by \(b_N\) and telescoping
from \(D_0=0\) proves the boxed congruence. The rational-polynomial
identities were independently checked after clearing unit denominators.
This proves \(U_N\equiv2\pmod5\) **only when**
\(5\nmid N\binom{2N}{N}\); dividing at other cutoffs requires further precision.

## Uniform symbolic partial result (not a cutoff sample)

`proof sketch`, supported by a coefficientwise `experiment` with explicit
infinite-tail bounds. Write \(e(N)=v_5(N)+v_5\binom{2N}{N}\).
There is an explicitly computed degree-25 polynomial \(P_{20}\in\mathbb Z[x]\),
coefficientwise congruent to 12 modulo25, for which **every** \(N\ge1\) satisfies
\[
D_N-125N^3b_NP_{20}(N)\in5^{23}\mathbb Z_5,\qquad
v_5(U_N-P_{20}(N))\ge20-3e(N).
\]
Consequently, for every cutoff with \(e(N)\le6\),
\[
U_N\equiv12\pmod{25},\qquad v_5(D_N)=3+3e(N).
\]
This includes infinitely many singular cutoffs: \(N=5(5^m+1)\) and
\(N=5^m+3\), \(m\ge1\), both have \(e(N)=1\). In contrast,
\(N=5^r\) and \(N=5^r-1\) have \(e(N)=r\), so this fixed certificate
does not establish their normalized law at arbitrary depth.

For distinct positive \(M,N\), the same certificate gives the partial
regularity estimate
\[
v_5(U_M-U_N)\ge\min\{2+v_5(M-N),\,20-3e(M),\,20-3e(N)\}.
\]
There is no replacement of the original all-cutoff conjecture by this
bounded-loss statement.

### Analytic construction and precision justification

Let \(\mathcal A=\mathbb Z_5\langle x\rangle\), the restricted power
series with integral coefficients tending to zero, and
\[
(LP)(x)=\frac{(2x+1)^3}{32}P(x+1)-x^3P(x).
\]
Put \(R(t)=\prod_{a=1}^4(5t+a)/24=1+E(t)\), where
\[
E(t)=125t/12+875t^2/24+625t^3/12+625t^4/24.
\]
For polynomial \(q\), let \((\mathscr S q)(N)=\sum_{j<N}q(j)\). Then
\[
\ell(x)=3\sum_{m\ge1}\frac{(-1)^{m+1}}m
\big((\mathscr S E^m)(2x)-2(\mathscr S E^m)(x)\big)-4x\log256
\]
converges in \(5\mathcal A\); \(H(x)=\exp\ell(x)\) agrees with the exact
integer-cutoff product above. To justify convergence, polynomial summation
of degree \(d\) loses at most \(\lfloor\log_5(d+1)\rfloor\) coefficient
valuation: use the integral changes of basis between monomials and falling
factorials and \(\mathscr S(x^{\underline j})=
x^{\underline{j+1}}/(j+1)\). The summand has valuation at least
\(3m-v_5(m)-\lfloor\log_5(4m+1)\rfloor\ge m+1\).
Terms of the exponential have valuation at least
\(j-v_5(j!)\ge3j/4\), and the degree-\(j\) coefficient of
\((a+5x)^{-3}\), \(a=1,2,3,4\), has valuation at least \(j\).
These bounds rigorously control all omitted infinite tails.

The exact analytic forcing is
\(f=(HB-5(6x+1))/125\). Coefficientwise expansion shows
\(f-L(12)\in25\mathcal A\), so in particular the division by125 is valid.
For a small independently checkable example, modulo \(5^6\),
\[
P_6=3637+1350x+8675x^2+7925x^3+7500x^5,
\]
and \(f\equiv LP_6\). The general exact checker computes \(HB-5(6x+1)\)
modulo \(5^{K+3}\) **before** dividing by125, and performs polynomial
reduction modulo \(5^K\). At \(K=20\), it gives
\(f-LP_{20}\in5^{20}\mathcal A\). Evaluating at every nonnegative integer,
multiplying by \(125b_N\), and telescoping the exact block recurrence proves
the uniform partial result. No finite list of cutoffs is used in that proof.

### Three constants still unresolved

The leading coefficient of \(L(x^d)\) is \(-3/4\), a 5-adic unit, in
degree \(d+3\). Descending polynomial division therefore gives quotient
and degree-at-most-two remainder maps of coefficient norm at most1.
By density of polynomials they extend to the exact direct sum
\[
\mathcal A=L(\mathcal A)\oplus\mathbb Z_5[x]_{\le2}.
\]
Thus \(f=LP+r_0+r_1x+r_2x^2\), uniquely, with
\(P\in12+25\mathcal A\). Telescoping from \(D_0=0\), rather than
choosing an arbitrary analytic solution, gives
\[
U_N=P(N)+\frac{\sum_{j=0}^2r_j\sum_{m=0}^{N-1}m^jb_m}{N^3b_N},
\]
where the \(j=0\) summand uses \(m^0=1\), including \(m=0\).
The actual initial value is \(U_1=-16008833/16777216\).
The certificate proves \(r_j\in5^{20}\mathbb Z_5\), **not** \(r_j=0\).
Exact vanishing proves the stronger restricted-analytic form of the
original Lipschitz conjecture. It was the remaining lemma of this
finite-precision approach; the linked Frobenius proof sketch addresses it
by an exact structural comparison, not by the certificate.

For the explicit block operator
\[
(\mathcal T g)(x)=H(x)\sum_{a=0}^4q_a(x)g(5x+a),\qquad
q_a(x)=\prod_{j=0}^{a-1}\frac{(10x+2j+1)^3}{32(5x+j+1)^3},
\]
block telescoping gives \(\mathcal T(Lg)=125L(H(x)g(5x))\).
It therefore acts on \(\mathcal A/L(\mathcal A)\), and the required
vanishing is exactly \(\mathcal T[6x+1]=5[6x+1]\) there. That identity
is the exact identity established in the linked reviewed proof sketch.
The finite-precision calculation alone cannot establish it; without that
structural argument a nonzero remainder would refute this restricted-analytic
mechanism, not automatically the weaker Lipschitz conjecture.

Polynomial reduction is established methodology; see
[Hou–Mu–Zeilberger, arXiv:1907.09391](https://arxiv.org/abs/1907.09391).
The bounded completion and this particular certificate have no novelty
claim attached. Independent expert review of the full argument is still
desirable; no Lean verification has been performed.

### Reproducing the symbolic certificate

The [symbolic checker](../../../../workflows/experiments/ramanujan_fiveadic_defect_20260906/symbolic.py)
and [full degree-25 certificate](../../../../workflows/experiments/ramanujan_fiveadic_defect_20260906/certificate20.json)
are self-contained. Run:

```sh
python3 workflows/experiments/ramanujan_fiveadic_defect_20260906/symbolic.py --precision 20
```

Independent reproduction matched every JSON field and separately checked
the coefficient identity, constant initial value and modulo25 polynomial.
Output precision is \(5^{20}\); raw forcing precision is \(5^{23}\).
An additional precision24 run also returned zero remainder, but no
infinite-precision conclusion is drawn and the retained partial result
uses the explicit precision20 certificate only.

## Reproducible cutoff experiment and scope

`experiment`: [exact modular checker](../../../../workflows/experiments/ramanujan_fiveadic_defect_20260906/check.py)
uses integers only, strips the full proposed valuation before unit inversion,
and adds a guard digit. Commands from the repository root:

```sh
python3 workflows/experiments/ramanujan_fiveadic_defect_20260906/check.py --max-n 1000 --precision 6
python3 workflows/experiments/ramanujan_fiveadic_defect_20260906/check.py --max-n 10000 --precision 10
```

Both passed independent reproduction. The latter computes each \(U_N\)
modulo \(5^{10}\), using working modulus \(5^{32}\); these are different
precisions. Every tested value is 12 modulo 25. Every pair in the range
satisfies the Lipschitz inequality truncated at output precision 10.
Comparisons with no two distinct cutoffs in a residue class are vacuous.
Independent exact rational arithmetic at \(N=1,\ldots,30\) also matched the
modular values and the exact block recurrence. The first five residues modulo
\(5^{10}\) are 294712, 9422562, 7497237, 4835037, 3296012;
they are **not** all 12 modulo \(5^{10}\).

## What this does not show

No occurrence, normality, CW0, CW9, E, or V1 conclusion follows. The positive
real tail supplies upper approximants \(4/S_N>\pi\), but a prescribed decimal
hit needs ordered residues of their full numerators and denominators. The
five-adic defect does not supply that information. An explicit number with
fractional digits only 1 and 2 stays in \([1/9,2/9]\) under every decimal
shift; nothing here yet rules out analogous avoidance for the Ramanujan limit.
The series identity alone is not a digit separator. This note and its linked
exact proof sketch add arithmetic information, not a digit solution strategy
with its missing bridge discharged.
