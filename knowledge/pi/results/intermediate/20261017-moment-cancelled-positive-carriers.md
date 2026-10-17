# Moment cancellation with a positive tail for Pythagorean π carriers

Date: 2026-10-17. Label: `proof sketch`, with an exact finite `experiment`.
No Lean verification or priority claim. No CW0 or V1 conclusion.

The [carry-route specification](../../workstreams/OPEN_PROBLEMS.md#p3-the-carry-certificate-reformulation)
requires compatible divisibility and a positive small tail. The
[Ramanujan reciprocal analysis](20260905-ramanujan-reciprocal-analysis.md)
records why separate control of those properties does not suffice. The
construction below changes the positive carrier itself: rational combinations
of Pythagorean arcsine series cancel arbitrarily many initial odd moments,
remove prime factors above an explicit cutoff from each rational truncation,
and retain an eventually positive real tail.

The [exact checker](../../../../workflows/experiments/positive_moment_carriers_20261017/audit.py)
and [certificate](../../../../workflows/experiments/positive_moment_carriers_20261017/certificate.json)
record the concrete rational data and checks. The infinite statements below
come from the written argument, not from the finite census.

## Result and scope

For every fixed integer \(K\ge1\), there are a positive integer \(q\) and
rational partial sums \(F_N\to q\pi/2\) such that the first \(K\) series
coefficients vanish and all coefficients are positive from a computable index
onward. Their real tails satisfy

\[
 \left|q\pi/2-F_N\right|
 \le B\frac{(16/25)^{N+1}}{2N+3}
\tag{1}
\]

for a fixed positive rational \(B\). If \(D_N\) denotes the part coprime
to \(10\) of the reduced denominator of \(F_N\), an elementary Chebyshev
estimate gives

\[
 \limsup_{N\to\infty}\frac{\log D_N}{N}
 \le\frac{2\log4}{2K+1}.
\tag{2}
\]

For the concrete \(K=3\) construction,

\[
 \boxed{0<D_N\left(q\pi/2-F_N\right)\longrightarrow0.}
\tag{3}
\]

The positivity holds for every \(N\ge56\). The multiplier \(D_N\)
depends on \(N\), and the remaining smooth denominator is large. Thus (3)
does not supply the fixed-multiplier witness required by the carry route.
An exact valuation theorem below identifies the cost of varying the
Gaussian exponents instead of assuming additional numerator divisibility.

## 1. Rational-angle nodes and moment polynomials

Take \(K+1\) primitive Pythagorean triples with distinct normalized leg sums,

\[
 a_i^2+b_i^2=c_i^2,\qquad 0<a_i\le b_i,\qquad
 c_i=5^{k_i},\qquad \frac{b_i}{c_i}\le\frac45.
\]

Put

\[
 x_i=\frac{a_i}{c_i},\qquad y_i=\frac{b_i}{c_i},\qquad
 s_i=x_i+y_i,\qquad t_i=s_i^2.
\]

There are arbitrarily many such triples. The real and imaginary parts of
\((3+4i)^j\), with absolute values and the two coordinates sorted, give
primitive triples of hypotenuse \(5^j\). The argument of \((3+4i)/5\) is
an irrational multiple of \(\pi\): if that number were a root of unity,
its sum with its inverse, \(6/5\), would be a rational algebraic integer.
Irrational rotation visits the open arc on which both absolute coordinates
are less than \(4/5\) infinitely often. Distinct positive exponents have
distinct \(t_i\), since equality would give a rational relation between
the argument and \(\pi\) through a quadrant symmetry.

The odd moments have the polynomial form

\[
 x_i^{2n+1}+y_i^{2n+1}=s_iP_n(t_i),
\]

where

\[
 P_0(t)=1,\qquad P_1(t)=\frac{3-t}{2},\qquad
 P_n(t)=P_{n-1}(t)-\frac{(t-1)^2}{4}P_{n-2}(t).
\tag{4}
\]

Indeed, the roots \(x_i^2,y_i^2\) have sum \(1\) and product
\(((t_i-1)/2)^2\). Thus \(P_n\) is a polynomial of degree \(n\):
its leading coefficient satisfies \(\ell_n=-\ell_{n-2}/4\) and never
vanishes.

## 2. Exact cancellation weights

Order the nodes so \(t_0<\cdots<t_K\), and define

\[
 d_i=\frac1{s_i\prod_{j\ne i}(t_i-t_j)},\qquad
 \lambda_i=\frac{d_i}{\sum_jd_j}.
\tag{5}
\]

The weights are rational. Their denominator is nonzero: \(\sum_jd_j\)
is the \(K\)th divided difference of \(f(t)=t^{-1/2}\), and has strict
sign \((-1)^K\) because \(f^{(K)}\) has that sign on \((0,\infty)\).
Consequently

\[
 \sum_i\lambda_i=1,\qquad
 \sum_i\lambda_i\left(x_i^{2n+1}+y_i^{2n+1}\right)=0
 \quad(0\le n<K).
\tag{6}
\]

The second identity is the barycentric divided-difference formula applied
to \(P_n\), whose degree is less than \(K\).

Let \(q\) be the positive least common multiple of the weight denominators
and let \(C=5^S\) be a common hypotenuse. Define integers

\[
 A_i=Cx_i,\quad B_i=Cy_i,\quad w_i=q\lambda_i,\qquad
 W_h=\sum_iw_i(A_i^h+B_i^h).
\]

Then \(W_1=W_3=\cdots=W_{2K-1}=0\). Integrating the binomial expansion
of the derivative of \(\arcsin\), uniformly on compact subintervals of
\((-1,1)\), gives

\[
 \boxed{
 \frac{q\pi}{2}=
 \sum_{n=0}^{\infty}
 \frac{\binom{2n}{n}W_{2n+1}}
 {4^nC^{2n+1}(2n+1)}.
 }
\tag{7}
\]

This is an identity for the actual constant \(\pi\), because
\(\arcsin x_i+\arcsin y_i=\pi/2\) for every node and
\(\sum_i\lambda_i=1\). Write \(F_N\) for the partial sum through
\(n=N\).

## 3. Eventual positivity and a uniform real rate

The weight \(\lambda_0\) is positive: its barycentric denominator and
\(\sum_jd_j\) both have sign \((-1)^K\). Moreover,

\[
 y(t)=\frac{\sqrt t+\sqrt{2-t}}2
\]

is strictly decreasing for \(1<t<2\). Thus \(y_0\) is uniquely largest
among the larger legs. Let

\[
 r=\max_{i>0}\frac{y_i}{y_0}<1,\qquad
 H=\sum_{i>0}|\lambda_i|,\qquad
 m_n=\sum_i\lambda_i(x_i^{2n+1}+y_i^{2n+1}).
\]

Then

\[
 m_n\ge y_0^{2n+1}\left(\lambda_0-2Hr^{2n+1}\right).
\tag{8}
\]

Choose \(n_0\) so \(4Hr^{2n_0+1}\le\lambda_0\). This inequality
persists for every \(n\ge n_0\), and
\(m_n\ge\lambda_0y_0^{2n+1}/2>0\). Hence the tail of (7) is strictly
positive for \(N\ge n_0-1\). Negative earlier coefficients do not
affect that conclusion.

Because every leg is at most \(4/5\) and
\(\binom{2n}{n}/4^n\le1\), replacing each later odd denominator by
\(2N+3\) and summing a geometric series proves (1) with

\[
 B=\frac{2q(\sum_i|\lambda_i|)(4/5)}{1-16/25}.
\tag{9}
\]

The prefactor may grow with \(K\); \(K\) is fixed in every asymptotic
statement.

## 4. Exact nonsmooth denominator bound

Put

\[
 X=2N+1,\qquad
 M=\max\left\{
  \left\lfloor\frac{X}{2K+1}\right\rfloor,
  \lfloor\sqrt X\rfloor
 \right\},
\]
\[
 U_N=\prod_{\substack{p\le M\\p\text{ prime},\ p\ne2,5}}
          p^{\lfloor\log_pX\rfloor}.
\]

Then

\[
 \boxed{D_N\mid U_N.}
\tag{10}
\]

All factors outside \(2\) and \(5\) in a term denominator of (7) come
from \(2n+1\), so the maximum possible exponent of \(p\) is
\(\lfloor\log_pX\rfloor\). It remains to exclude \(p>M\). Such a
prime satisfies \(p^2>X\). Whenever \(p\mid2n+1\), write
\(2n+1=hp\). The strict inequality \(p>X/(2K+1)\) gives odd
\(h<2K+1\), hence \(h\in\{1,3,\ldots,2K-1\}\). Fermat's congruence
and (6) give

\[
 W_{hp}=\sum_iw_i(A_i^{hp}+B_i^{hp})
 \equiv\sum_iw_i(A_i^h+B_i^h)=W_h=0\pmod p.
\]

The single denominator factor \(p\) therefore cancels in that term.
Every summand is \(p\)-integral, so \(F_N\) is \(p\)-integral. This
proves (10). The square-root cutoff is essential to the all-\(N\)
statement: cancelling one factor \(p\) does not itself cancel a
possible denominator \(p^2\).

For fixed \(K\) and large \(N\), \(M=\lfloor X/(2K+1)\rfloor\).
With \(\vartheta(v)=\sum_{p\le v}\log p\),

\[
 \log U_N\le\vartheta(M)+
 \sum_{e=2}^{\lfloor\log_2X\rfloor}\vartheta(X^{1/e}).
\tag{11}
\]

The higher-power sum is \(O(\sqrt X\log X)\), using the elementary
bound \(\vartheta(v)=O(v)\). Primes in a dyadic interval
\((v/2,v]\) divide an appropriate central binomial coefficient, whose
logarithm is at most \(v\log2+O(\log v)\). Summing over dyadic
intervals gives

\[
 \vartheta(v)\le v\log4+O((\log v)^2).
\]

Substitution in (11) yields

\[
 \log D_N\le\frac{\log4}{2K+1}X+o(X),
\tag{12}
\]

which proves (2). If desired, the prime number theorem sharpens
\(\log4\) in (12) to \(1\); that sharpening is not used below.

## 5. Concrete four-angle instance

Take \(K=3\) and Gaussian exponents \(1,6,11,16\).

| Exponent | Smaller leg | Larger leg | Hypotenuse |
|---|---:|---:|---:|
| 1 | 3 | 4 | 5 |
| 6 | 10296 | 11753 | 15625 |
| 11 | 34182196 | 34867797 | 48828125 |
| 16 | 98248054847 | 116749235904 | 152587890625 |

Every larger leg is at most \(4/5\) of its hypotenuse. The certificate
records the exact weights and \(q\). The dominance inequality (8) holds
from \(n_0=57\), so the infinite tail is positive for every \(N\ge56\).
Combining (1) and (12),

\[
 \limsup_{N\to\infty}\frac1N
 \log\left(D_N(q\pi/2-F_N)\right)
 \le\log(16/25)+\frac{2\log4}{7}<0.
\tag{13}
\]

The strict inequality has the integer certificate

\[
 16^8=4294967296<6103515625=25^7.
\]

Thus the nonsmooth-cleared tail is positive and tends to zero. This proof
needs no prime number theorem. Substituting the explicit \(U_N\) into
(1) gives the following exact bounds for the infinite tail.

| \(N\) | Bound for \(U_N\lvert q\pi/2-F_N\rvert\) |
|---:|---:|
| 1000 | \(<10^{-17}\) |
| 2000 | \(<10^{-87}\) |
| 4000 | \(<10^{-215}\) |

## 6. Exact five-adic cost of changing the Gaussian exponents

The natural attempt to obtain additional numerator divisibility by varying
the Gaussian exponents admits an exact valuation calculation. Relabel the
same nodes by increasing exponent,

\[
 k_0<k_1<\cdots<k_K=S,\qquad
 v_0=k_0+2\sum_{j=1}^Kk_j.
\]

This order need not agree with the real order \(t_0<\cdots<t_K\) used
for the positive-tail argument. Here \(v_5(s_i)=-k_i\), because
\(a_i+b_i\) is a five-adic unit. Distinct valuations give

\[
 v_5(t_i-t_j)=-2\max(k_i,k_j).
\]

The unnormalized weight \(d_i\) consequently has valuation

\[
 v_i=(2i+1)k_i+2\sum_{j>i}k_j,\qquad
 v_{i+1}-v_i=(2i+1)(k_{i+1}-k_i)>0.
\tag{14}
\]

Thus \(\sum_i d_i\) has the unique minimum valuation \(v_0\). Every
\(\lambda_i\) is five-adically integral,
\(v_5(\lambda_i)=v_i-v_0\), and \(q\) is coprime to \(5\).
For odd \(h\), \(a_i^h+b_i^h\) is a five-adic unit: modulo \(5\)
the ratio \(a_i/b_i\) is \(2\) or \(3\), and an odd power of either
cannot be \(-1\).

For \(h=2n+1\), the valuation difference between the contributions of
nodes \(i+1\) and \(i\) to \(m_n\) is

\[
 (2i+1-h)(k_{i+1}-k_i)=2(i-n)(k_{i+1}-k_i).
\]

For \(n\ge K\) every difference is strictly negative. The node of
largest hypotenuse is uniquely dominant five-adically, yielding

\[
 \boxed{v_5(m_n)=-v_0-2(n-K)S\qquad(n\ge K).}
\tag{15}
\]

Let \(T_n\) be the \(n\)th summand of (7). Then

\[
 v_5(T_n)=v_5\binom{2n}{n}-v_5(2n+1)-v_0-2(n-K)S.
\tag{16}
\]

For \(n\ge K+1\), the change in this valuation is

\[
 -2S+2v_5(2n-1)-v_5(n)-v_5(2n+1),
\tag{17}
\]

using the adjacent-factor quotient
\(2(2n-1)^2/[n(2n+1)]\) of the binomial-over-odd-denominator factors.
If \(2N-1<5^S\), every change through \(n=N\) is at most \(-2\).
The first \(K\) summands vanish, so the final term is uniquely dominant:

\[
 \boxed{v_5(F_N)=v_5(T_N)
 \qquad(K\le N,\ 2N-1<5^S).}
\tag{18}
\]

This valuation is negative. The number of base-five carries in
\(N+N\), and hence \(v_5\binom{2N}{N}\), is at most the number of
base-five digits of \(2N\). In the displayed range that number is at
most \(S+1\), whereas \(v_0\ge2S+1\). Therefore the reduced numerator
of \(F_N\) is a five-adic unit. Multiplying by \(D_N\) preserves this
fact. Enlarging the Gaussian exponents in this range increases the forced
smooth denominator; it does not create an extra numerator factor \(5\).

Equations (15)-(18) hold for every ordered exponent set, not just the
four-node example. Equations (15)-(16) have no upper bound on \(n\).
No claim is made about cancellation in \(F_N\) outside the range of
(18). The audit checks these identities exactly throughout its finite
coefficient and prefix census.

## 7. What is still missing for decimal digits

For \(N\ge56\), \(D_NF_N\in\mathbb Z[1/10]\), and

\[
 D_Nq\pi/2=D_NF_N+\varepsilon_N,
 \qquad \varepsilon_N>0,\quad \varepsilon_N\longrightarrow0.
\]

The odd-moment cancellation removes large nonsmooth denominator factors;
the positive-tail dominance and the denominator estimate hold at the same
time. The rational-angle identity (7) supplies the actual-\(\pi\)
arithmetic behind that statement.

Two operations remain missing for the carry route. First, \(D_N\) varies
with \(N\), whereas decimal words concern the fixed number \(\pi\),
or an allowed fixed rational multiple handled by a valid transfer. Second,
turning \(D_NF_N\) into an integer requires powers of \(2\) and \(5\)
whose growth can overwhelm (1). The completely cleared error is not
controlled. Nor is an ordered numerator residue selected for a prescribed
word.

This is supporting arithmetic, not an active V1 candidate. The weaker
approximation conclusion alone has an immediate separator: for any
irrational real \(\alpha\), its decimal truncations give positive errors
tending to zero with \(D_N=1\), including when \(\alpha\) avoids a word.
Those truncations do not reproduce identity (7); they show why the final
approximation property by itself is insufficient. A new admissible input
must use (7) to supply a fixed-multiplier or target-oriented statement
which that replacement cannot share.

## Reproduction

From the repository root, run

```sh
python3 workflows/experiments/positive_moment_carriers_20261017/audit.py \
  --output workflows/experiments/positive_moment_carriers_20261017/certificate.json
```

The standard-library checker verifies exact weights and cancelled moments,
the positivity-threshold constant, coefficients and denominator divisibility
through \(N=160\), the five-adic identities, and selected exact bounds from
the proved infinite-tail majorant. Its 4593 prime checks and finite signs
are `experiment`; they are not evidence for an unbounded word-occurrence
claim.
