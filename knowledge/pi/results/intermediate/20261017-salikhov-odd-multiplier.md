# Odd Salikhov multiplier cancellation and compatible five-adic forcing

Date: 2026-10-17. Labels: `proof sketch` and `experiment`. No Lean, novelty, or decimal-distribution claim.

The source normalization is [Zeilberger–Zudilin, Part II](https://arxiv.org/html/1912.06345v2),
as developed in the [local-pair note](20260906-salikhov-mod5-support.md).
The five-adic intersection below uses the
[forced-divisor theorem](20261016-salikhov-forced-divisor.md) from PR #11.

This note uses the exact modified Salikhov normalization from
[Zeilberger--Zudilin, arXiv:1912.06345v2, Part II](https://arxiv.org/html/1912.06345v2)
and the [existing local-pair note](20260906-salikhov-mod5-support.md):

\[
I_n=a_n+b_n\pi,\qquad q_n=2^{2-\lfloor5n/2\rfloor}b_n.
\]

## Odd-index congruence

For integers \(L\ge3\), \(m\ge1\), put \(N=2^L m\) and \(n=N+1\).
Then

\[
\boxed{q_{N+1}\equiv1196\binom N{N/4}\pmod{2^{L+1}}.}
\tag{1}
\]

Consequently, if \(s_2(3m)\le L-2\), then

\[
\boxed{v_2(q_{1+2^L m})=2+s_2(3m).}
\tag{2}
\]

There is no oddness restriction on \(m\). Factorial valuations give
\(v_2\binom N{N/4}=s_2(3m)\) for every positive \(m\).

### Ramified normalization

Work in \(\mathcal O=\mathbb Z_2[\tau]\), \(\tau^2=2\), and put

\[
h(z)=1-7\tau z+39z^2-50\tau z^3+50z^4,\qquad
U(z)=\frac{(1-2\tau z)^2h(z)^2}{(1-\tau z)^3}.
\]

Substituting \(w=2\tau z\) in the published partial-fraction coefficient
formula gives, for odd \(n\),

\[
q_n=-\tau[z^{3n}]\frac{U(z)^n}{1-\tau z}.
\tag{3}
\]

In detail, the original coefficient is
\(A_{n,0}=[w^{3n}](w-1)^{2n}H(w)^{2n}/(2-w)^{3n+1}\), where
\[
H(w)=25(w-1)^4+6(w-1)^2+1
=32-112w+156w^2-100w^3+25w^4,
\]
and \(H(2\tau z)=32h(z)\). The scaling factor is
\(2^{5n/2-1}\), while
\(q_n=(-1)^n2^{1-\lfloor5n/2\rfloor}A_{n,0}\).
For odd \(n\), the remaining factor is \(-\tau\).
Each coefficient of an even power of \(z\) in \(U\) lies in
\(\mathbb Z_2\), and each odd coefficient lies in
\(\tau\mathbb Z_2\); the same property is preserved by all products
and inverses with constant term 1 below. Thus multiplying an odd
coefficient by \(-\tau\) produces a rational two-adic integer.

In \(\mathcal O/2\mathcal O\), where \(\tau^2=0\),

\[
U(z)\equiv (1+z^4)(1+\tau z)\pmod{2\mathcal O[[z]]}.
\tag{4}
\]

For \(A-B\in2\mathcal O[[z]]\) and \(2^L\mid N\), the binomial
expansion proves \(A^N-B^N\in2^{L+1}\mathcal O[[z]]\): its
\(j\)-th term has valuation at least
\(j+L-v_2(j)\ge L+1\).
Use this with (4) in (3), keeping one factor of \(U\) outside the
lift. The resulting error is divisible by \(2^{L+1}\) in the rational
coefficient after multiplication by \(-\tau\).

Also,

\[
(1+\tau z)^N\equiv1\pmod{2^L\mathcal O[[z]]},
\tag{5}
\]

because
\(v_2\binom Nj+j/2\ge L-v_2(j)+j/2\ge L\) for every
\(1\le j\le N\). On multiplying the odd coefficient by \(-\tau\),
the rational error from (5) is divisible by \(2^{L+1}\).
Therefore

\[
q_n\equiv-\tau[z^{3n}]
  \frac{U(z)}{1-\tau z}(1+z^4)^N\pmod{2^{L+1}}.
\tag{6}
\]

### The fixed coefficient tail

Set

\[
H_\ell=-\tau[z^{4\ell+3}]\frac{U(z)}{1-\tau z}.
\]

Direct degree-three extraction gives \(H_0=1196\), with
\(v_2(H_0)=2\). For all \(\ell\ge0\),

\[
H_\ell\in2^{2\ell}\mathbb Z.
\tag{7}
\]

To see this without an asymptotic argument, substitute \(y=\tau z\)
and define the integral polynomial

\[
J(y)=2-14y+39y^2-50y^3+25y^4.
\]

Then

\[
\frac{U(z)}{1-\tau z}
=\frac{(1-2y)^2J(y)^2}{4(1-y)^4},
\quad
H_\ell=-2^{2\ell}[y^{4\ell+3}]
 \frac{(1-2y)^2J(y)^2}{(1-y)^4}.
\]

Put \(R=3N/4\). Extracting the coefficient in (6) gives

\[
q_n\equiv\sum_{\ell=0}^{R}H_\ell\binom N{R-\ell}
\pmod{2^{L+1}}.
\tag{8}
\]

Terms with \(2\ell\ge L+1\) vanish by (7). Every remaining
\(1\le\ell\le\lfloor L/2\rfloor\) satisfies
\(\ell<2^{L-2}\), since \(L\ge3\). As \(2^{L-2}\mid R\),
we have \(v_2(R-\ell)=v_2(\ell)\). Hence

\[
v_2\left(H_\ell\binom N{R-\ell}\right)
\ge2\ell+L-v_2(\ell)\ge L+2.
\]

Only \(\ell=0\) remains in (8). Symmetry of binomial coefficients
proves (1), and \(v_2(1196)=2\) plus the stated digit-sum condition
proves (2).

## An explicit odd family compatible with forced powers of five

For each integer \(a\ge1\), set

\[
L_a=3a+4,\qquad
m_a\in\{1,\ldots,5^a-1\},\qquad
2^{L_a+1}m_a\equiv-1\pmod{5^a},
\]

and \(n_a=1+2^{L_a}m_a\). The residue \(m_a\) exists uniquely,
since 2 is invertible modulo \(5^a\), and is nonzero. Then

\[
v_5(2n_a-1)\ge a,\qquad
v_5(q_{n_a})\ge a,
\]

where the latter statement uses the independently proved forced-divisor
theorem. Moreover \(3m_a<3\cdot5^a<2^{3a+2}\), so
\(s_2(3m_a)\le3a+2=L_a-2\). Equation (2) therefore gives

\[
v_2(q_{n_a})=2+s_2(3m_a)\le L_a.
\]

This is an unbounded family: \(n_a\ge1+2^{L_a}\).
The elementary size upper bound is \(n_a<1+16\cdot40^a\).

Write \(-a_n/b_n=P_n/Q_n\) in lowest terms with positive denominator,
and let \(c_n=2^{2-\lfloor5n/2\rfloor}a_n\). Using the repository's
proved-in-prose companion bound
\(v_2(c_n)\ge2n+1-\lfloor\log_2(4n+1)\rfloor\), we obtain

\[
\boxed{v_2(P_{n_a})\ge2n_a-1-2\lfloor\log_2n_a\rfloor,
\qquad Q_{n_a}\text{ is odd}.}
\]

Indeed \(L_a\le\lfloor\log_2n_a\rfloor\), and
\(\lfloor\log_2(4n+1)\rfloor=\lfloor\log_2n\rfloor+2\) for
positive integral \(n\). The resulting lower bound is positive for
this family.

The five-adic assertion concerns the unreduced multiplier. It does not
assert that the same five-adic precision survives in \(Q_{n_a}\), because
the rational companion may cancel it. No ordered decimal residue or target
hit is supplied. This is not an admitted V1 candidate.

## Exact finite-precision evaluator

The checker also evaluates the two-adic multiplier valuation at very large
indices without constructing the full integer. The following is its
all-index truncation argument; it does not assert an all-index asymptotic
bound on the returned valuation.

The root-coordinate residue identity is

\[
q_n=2^{-\lfloor5n/2\rfloor}[t^{3n}]
(1+t)^{n-1/2}(32+56t+25t^2)^{2n}.
\]

For \(j\ge0\), define the odd two-adic unit

\[
u_{n,j}=\frac{\prod_{r=0}^{j-1}(2n-1-2r)}{j!/2^{v_2(j!)}}.
\]

Legendre's factorial formula gives
\(\binom{n-1/2}{j}=2^{-2j+s_2(j)}u_{n,j}\).
Let \(h=\lfloor n/2\rfloor\), \(s_0=\lceil n/2\rceil\), and
\(\delta=n\bmod2=s_0-h\). Group the multinomial expansion by
\(s\), the number of constant-or-linear factors of
\(32+56t+25t^2\), and \(b\), the number among them selecting the
linear term. The remaining binomial-series index is \(j=2s-b-n\).
Combining the powers of two gives the exact identity

\[
q_n=\sum_{s=s_0}^{2n}\binom{2n}s25^{2n-s}
 \sum_{b=0}^{\min(s,2s-n)}
 \binom sb7^b2^{s-h+s_2(2s-b-n)}u_{n,2s-b-n}.
\tag{9}
\]

Every term with \(s=s_0+\ell\) has valuation at least
\(\delta+\ell\). Modulo \(2^M\), it therefore suffices to retain

\[
0\le\ell\le\min(2n-s_0,M-\delta-1),\qquad
0\le j\le2\ell+\delta<2M.
\tag{10}
\]

Each omitted term is individually zero modulo \(2^M\). This is exact
truncation, with no floating-point arithmetic or assumed cancellation.

To avoid constructing the large binomial coefficient, write

\[
e_s=v_2\binom{2n}s=s_2(s)+s_2(2n-s)-s_2(n),\qquad
O_s=2^{-e_s}\binom{2n}s.
\]

Divide (9) by the common odd unit
\(O_{s_0}25^{2n-s_0}\). Its \(s=s_0+\ell\) outer factor becomes
\(2^{e_s}(O_s/O_{s_0})25^{-\ell}\). The unit quotient is updated
using
\(\binom{2n}{s+1}/\binom{2n}s=(2n-s)/(s+1)\), tracking powers of
two separately and inverting only odd parts. Similarly,
\[
u_{n,j}=u_{n,j-1}\frac{2n+1-2j}{j/2^{v_2(j)}}.
\]
The checker returns the residue after division by that common odd unit,
so a nonzero residue determines \(v_2(q_n)\) exactly. A zero residue
only certifies \(v_2(q_n)\ge M\); the precision is then increased.
There are \(O(M^2)\) small-index terms. No claim is made that
\(M=O(\log n)\) suffices for every \(n\), or for every special
index \(N_k=(5^k+1)/2\).

## Reproduction and review

Run the [standard-library checker](../../../../workflows/experiments/salikhov_odd_multiplier_20261017/odd_branch.py)
and optionally save its [certificate](../../../../workflows/experiments/salikhov_odd_multiplier_20261017/certificate.json):

```sh
python3 workflows/experiments/salikhov_odd_multiplier_20261017/odd_branch.py
python3 workflows/experiments/salikhov_odd_multiplier_20261017/odd_branch.py --json workflows/experiments/salikhov_odd_multiplier_20261017/certificate.json
```

The default run compares the truncated evaluator with full exact rational
coefficient extraction for \(n=1,\ldots,50\). At all 25 odd indices
in that range, it also checks an independent integer expansion in the
ramified coordinate. A separate factorial-unit modular implementation
checks congruence (1) at all \(3\le L\le12\), \(1\le m\le79\):
400 odd \(m\) cases and 390 even \(m\) cases. It checks the predicted
two-adic valuation and defining five-adic index congruence on the first
20 CRT parameter choices. It also records exact two-adic valuations for
\(N_k=(5^k+1)/2\), \(1\le k\le100\), as a finite `experiment`.
The latter table is not an all-\(k\) bound, and the CRT checks do not
compute the five-adic reduced denominator.

The odd normalization, both ramified lifting estimates, the fixed-tail
bound, binomial valuations, CRT construction, and reduced-numerator
conclusion were reviewed independently. A second review explicitly
checked that the extra factor of two in (5)--(6) follows from the odd
coefficient lying in \(\tau\mathbb Z_2\), including when \(m\) is
even. The mathematical labels remain `proof sketch` and `experiment`.


The CRT parametrization need not be injective: parameters 14 and 15 in the
recorded range select the same index. The lower bound on the selected
index proves unboundedness; the certificate counts parameter choices.
