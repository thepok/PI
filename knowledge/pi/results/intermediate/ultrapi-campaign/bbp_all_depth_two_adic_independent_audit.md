# Independent audit of the BBP all-depth two-adic attack

Audit date: **2026-08-12 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825.

Audited artifacts:

- [bbp_all_depth_two_adic_attack.md](bbp_all_depth_two_adic_attack.md),
  SHA-256
  9c1282724c7999fd67133a3f0e756015e564dc6b7a2a1ec44f2efe892b2653d9;
- [bbp_all_depth_two_adic_check.py](bbp_all_depth_two_adic_check.py),
  SHA-256
  552c7e49e7925578e78fb7b77205e12c193756bc9dc6b93c8c7ef1fcf33c2f03.

## Verdict

**PASS after one audited quantifier correction.** The central all-depth
valuation formula, its fixed-\(16\) consequence, the checker, and the source
scopes pass the audit.

The first version's broader opening claim for “every fixed nonzero integer
\(c\)” was literally false if read uniformly over every \(n\): for
\(c=10^{n_0}\), taking \(n=n_0\) makes
\((10^n-c)B_N=0\in\mathbb Z\) for every \(N\). The report was amended to
quantify both depth and exponent as sufficiently large, exactly matching the
argument in Section 5. The amended report hash is frozen above. No change was
needed to the stated \(c=16,\ N\geq2,\ n\geq5\) result.

With that correction, the mathematical derivation is a sound
proof sketch. It does not prove a fixed-sixteen return and does not change
canonical V1 from conjecture.

## 1. Reflected coefficient and analytic convergence

Independent substitution in

\[
 a(X)=\frac4{8X+1}-\frac2{8X+4}-\frac1{8X+5}-\frac1{8X+6}
\]

gives

\[
 a(-1-j)=\frac1{8j+2}+\frac1{8j+3}
          +\frac2{8j+4}-\frac4{8j+7}.
\]

Putting this over a common denominator cancels every factor of \(2\) and
gives exactly

\[
 \frac{120j^2+89j+16}
 {(2j+1)(4j+1)(8j+3)(8j+7)}.
\]

The compact expression

\[
 a(X)=\frac{120X^2+151X+47}
 {(2X+1)(4X+3)(8X+1)(8X+5)}
\]

also checks. Its denominator is \(1\) modulo \(2\) in
\(\mathbb Z_2[X]\), so its reciprocal is one global restricted power series
on the closed unit disc. Translation by any \(j\in\mathbb Z_2\) preserves a
Gauss-norm bound of \(1\). Therefore

\[
 F(X)=\sum_{j\geq0}16^j a(X-1-j)
\]

converges in \(\mathbb Z_2\langle X\rangle\), not merely pointwise. This
justifies coefficientwise reduction modulo \(2\), evaluation at every
\(m\in\mathbb Z_2\), and later division by \(X\).

## 2. Null identity and the global primitive issue

Set

\[
 P(x)=x+x^2+2x^3-4x^6,
 \qquad g(x)=\frac{P(x)}{1-16x^8}.
\]

The geometric expansion is valid on the closed two-adic unit disc. After
termwise formal integration, the four coefficients in block \(j\) have
valuations

\[
 4j-1,\quad 4j,\quad 4j-1,\quad 4j+2,
\]

respectively. They tend uniformly to infinity, so the integrated series is
a single restricted power series \(H\in\mathbb Q_2\langle x\rangle\) with
\(H(0)=0\) and \(H'=g\). Its value \(H(1)\) is precisely the reflected
series in the report.

Both polynomial factorizations check exactly and reduce \(g\) to

\[
 g(x)=\frac{x(x-1)}{(2x^2-1)(2x^2-2x+1)}.
\]

Choose \(i^2=-1\) in \(\mathbb C_2\). Then
\(v_2(1-i)=v_2(1+i)=1/2\). Each of

\[
 1-2x^2,\quad 1+2x^2-2x,\quad
 1+(i-1)x,\quad 1-(1+i)x
\]

is \(1\) plus a polynomial of Gauss norm strictly below \(1\). Thus every
logarithm used in the proposed \(A(x)\) and \(G(x)\) converges as one global
power series on the disc. Direct symbolic differentiation independently
gives

\[
 A'(x)=\frac1{2x^2-2x+1},\qquad G'(x)=g(x).
\]

There is a real p-adic subtlety here: a locally analytic function with zero
derivative need not be globally constant on the totally disconnected space
\(\mathbb Z_2\). It does not create a gap in this report because both \(H\)
and \(G\) are **single global power series about zero**. Hence
\((H-G)'=0\) coefficientwise in characteristic zero, so \(H-G\) is a
constant; equality at zero gives \(H=G\).

At \(x=1\), the logarithm arguments are \(-1,1,i,-i\). All lie in
\(1+\mathfrak m_{\mathbb C_2}\). The convergent logarithm is a homomorphism
there and kills torsion, so their logarithms vanish. Consequently

\[
 H(1)=G(1)-G(0)=0,
\]

which proves the two-adic null identity and \(F(0)=0\). No real value of pi
is used in this cancellation.

## 3. Unit factor, tail separation, and denominator formula

All \(j\geq1\) summands of \(F\) vanish modulo \(2\). The \(j=0\) term is

\[
 a(X-1)=\frac{120X^2-89X+16}
 {(2X-1)(4X-1)(8X-7)(8X-3)}\equiv X\pmod2.
\]

Since \(F(0)=0\) and \(F\in\mathbb Z_2\langle X\rangle\), division by \(X\)
gives \(F=XU\) with \(U\in\mathbb Z_2\langle X\rangle\) and
\(U\equiv1\pmod2\). Therefore \(U(m)\) is a unit and

\[
 v_2(F(m))=v_2(m)\qquad(m\geq1).
\]

For \(m=N+1\), exact index reversal gives

\[
 S_N=16^N B_N=\sum_{j=0}^{m-1}16^j a(m-1-j).
\]

The omitted terms of \(F(m)\) start at \(j=m\). Because \(a\) maps
\(\mathbb Z_2\) into \(\mathbb Z_2\), their sum has valuation at least
\(4m\). Since \(4m>v_2(m)\), the ultrametric equality case yields

\[
 v_2(S_N)=v_2(m),\qquad
 v_2(B_N)=v_2(N+1)-4N.
\]

For \(N\geq1\) this is negative, so reduction of the rational cannot cancel
the indicated denominator power. Thus

\[
 \boxed{v_2(\operatorname{den}B_N)=4N-v_2(N+1)}
\]

is correctly derived at every depth \(N\geq1\).

For \(n>v_2(c)\), unequal valuations give

\[
 v_2(10^n-c)=v_2(c).
\]

Hence sufficiently large \(N,n\) cannot satisfy denominator divisibility.
For \(c=16\), the multiplier has valuation exactly \(4\) for \(n\geq5\),
whereas the denominator exponent is at least \(8\) for \(N\geq2\). The
fixed-\(16\) exact-anchor exclusion is therefore correct. The report also
correctly says this supplies no lower bound for the nonzero circle phase and
does not imply the desired return.

## 4. Source audit

The cited primary-source scopes were checked against the pinned local copies
and the official/arXiv records on 2026-08-12 UTC.

- Bailey--Borwein--Plouffe, Theorem 1, states the classical series used for
  \(B_N\) and derives it from an integral. Pinned PDF SHA-256:
  e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4.
- Barsky--Muñoz--Pérez-Marco, Theorem 5.2, restates and derives the classical
  BBP formula, while Proposition 5.3 gives a real null BBP formula. The
  report accurately says this source does **not** state its new formula (2)
  or two-adic reflected identity (3). Pinned PDF SHA-256:
  64629d2323ad8e1a11b457b3572c1568993c29b37e3959e8e9d31fa03d06fa2f.
- Lagarias, especially Theorem 4.1, presents the BBP remainder dynamics and
  explicitly conditional weak/strong dichotomy consequences. It does not
  provide an unconditional density result for pi. Pinned PDF SHA-256:
  a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9.

The report's source descriptions stay within those scopes. The recorded
negative search is appropriately described as bounded and is not promoted
to a novelty claim. This part is literature-checked as of the audit date.

## 5. Independent replay

[bbp_all_depth_two_adic_independent_check.py](bbp_all_depth_two_adic_independent_check.py)
does not import the primary checker. It pins the target and all three local
source PDFs, rechecks the rational reflection, uses independent symbolic
factorization and differentiation, verifies the all-depth denominator
formula through depth \(320\), and checks finite tail separation. Its
finite output has status experiment only.

Run:

    .venv/bin/python -m py_compile \
      work/ultrapi-resume/bbp_all_depth_two_adic_independent_check.py
    .venv/bin/python \
      work/ultrapi-resume/bbp_all_depth_two_adic_independent_check.py

Both commands passed. Independent checker SHA-256:
6e5afd5368fb2d52c85a4e4c17620dce169a00edf70d49558c654b5fa63289bd.

## Claim-status boundary

After the audited quantifier correction above, the all-depth two-adic
denominator result has status proof sketch; its finite replay is an
experiment; and the bounded source audit is literature-checked. It is
not machine-checked, a candidate resolution, or a verified resolution.
Canonical V1 remains a conjecture.
