# Source 017: decimal-prefix interpolation audit

Status: `proof sketch`, with exact finite `experiment` checks. This is a
scoped negative audit of possible modifications of openai/math family 017,
not an admitted V1 candidate or a new occurrence theorem for pi.

## 1. The source parameter regime requires an exponent greater than two

Suppose positive parameters satisfy

\[
0<\theta<A<B<1,\qquad C>1,\qquad B<1/C,\qquad B<C\theta.
\]

Then \(B^2<\theta\), and consequently

\[
\frac{A-\theta}{1-\theta}
 < \frac{\sqrt\theta-\theta}{1-\theta}
 = \frac{\sqrt\theta}{1+\sqrt\theta}<\frac12.
\]

Thus the additional approximation gap
\(\nu(A-\theta)>1-\theta\) necessarily implies \(\nu>2\).
This is an obstruction within the source's stated parameter regime, not a
claim that every possible interpolation argument has the same limitation.

Conversely, every \(\nu>2\) admits these parameters. Choose rational
\(1/2<b<1-1/\nu\), then rational
\(0<\delta<\min(1,(2b-1)/b^2)\). Put
\(\theta=1-\delta\), \(A=1-b\delta\). Then
\(A^2<\theta<A\) and
\(\nu(A-\theta)-(1-\theta)=[\nu(1-b)-1]\delta>0\).
Choose rational \(A/\theta<C<1/A\), then
\(A<B<\min(1/C,C\theta)\). This is the source's sufficiency
construction with an explicit bound on \(\delta\). A small positive
\(\eta\) also retains its stronger gap
\(\nu(A(1-\eta)-\theta)>(1-\theta)\). Thus feasibility in this
parameter regime is exactly \(\nu>2\).

For comparison, let a real \(x\) have no occurrence of \(0^k\) in its
greedy decimal expansion after the decimal point. For \(n\ge1\), put
\(q_n=10^n\) and \(a_n=\lfloor q_nx\rfloor\). Then

\[
10^{-(n+k)}\le x-a_n/q_n<10^{-n}.
\]

Indeed the first \(k\) digits of \(\{10^n x\}\) include a nonzero
digit. Therefore the effective approximation exponent

\[
\nu_n=-\frac{\log(x-a_n/q_n)}{\log q_n}
\]

satisfies \(1<\nu_n\le1+k/n\). In particular, under failure of CW0,
these truncations, with the specified denominators 10^n, eventually cannot
enter the source's exponent regime. No assertion about their reduced
denominators is made here.
This last assertion is about zero-word avoidance; arbitrary word avoidance
does not impose the same bound on zero runs.

## 2. Complete prime-power residue representatives

Fix a deleted decimal digit \(d\). Let \(S_N\) be the integers encoded
by exactly \(N\) digits from \(\{0,\ldots,9\}\setminus\{d\}\), with
the usual positional interpretation. For either \(p=2\) or \(p=5\),
\(S_N\) maps onto \(\mathbb Z/p^N\mathbb Z\).

Proof by induction: the allowed digits contain a representative of every
class modulo \(p\). Given a target \(b\bmod p^{N+1}\), choose an
allowed last digit \(a\equiv b\bmod p\). Since \(10/p\) is a unit
modulo \(p^N\), the congruence

\[
y\equiv ((b-a)/p)(10/p)^{-1}\pmod{p^N}
\]

has an allowed \(N\)-digit representative by the induction hypothesis.
The integer \(10y+a\) has the desired residue and allowed digits.

The representatives for \(2^N\) and \(5^N\) can differ. No assertion
of joint surjectivity modulo \(10^N\) is made.

For any nonempty forbidden word, choose a digit appearing in that word.
Deleting that digit gives a subset of its word-avoiding prefixes. Hence
the same primewise surjectivity holds for the entire word-avoiding prefix
set as well.

## 3. High degree with proportional jets: an all-precision bound

The low-degree residue argument has an extension when the proposed common
divisor must divide a packet of Taylor coefficients at every allowed center.

**Lemma.** Let \(p\) be prime and \(N\ge1\). Let
\(a_1,\ldots,a_M\in\mathbb Z\), where \(M=p^N\), be one
representative of each class modulo \(p^N\). For an integer \(t\ge0\)
and \(F\in\mathbb Q[X]\) of degree less than \(M(t+1)\),

\[
\inf_{x\in\mathbb Z}v_p(F(x))
\ge
\min_{1\le i\le M,\ 0\le j\le t}
 v_p\bigl(F^{[j]}(a_i)\bigr),
\tag{H}
\]

where \(F^{[j]}(a)=[Z^j]F(a+Z)\) is the Hasse/Taylor coefficient
and \(v_p(0)=+\infty\).

In particular, for every integer \(s\), if all displayed Taylor
coefficients lie in \(p^s\mathbb Z_{(p)}\), then every integer
value of \(F\) lies in \(p^s\mathbb Z_{(p)}\). There is no upper
bound on \(s\), \(t\), or the degree apart from the displayed
degree-versus-jet condition.

### Proof of the lemma

Define the cardinal polynomial

\[
L_i(X)=\prod_{\ell\ne i}\frac{X-a_\ell}{a_i-a_\ell}.
\]

For \(0\le j\le t\), let \(T_{ij}(Z)\) be the Taylor polynomial
through degree \(t-j\) of \(L_i(a_i+Z)^{-(t+1)}\), and set

\[
H_{ij}(X)=(X-a_i)^j L_i(X)^{t+1}T_{ij}(X-a_i).
\]

The degree is at most \(M(t+1)-1\). At \(a_i\), its Taylor packet
through degree \(t\) is exactly \(Z^j\); at every other center the
packet is zero. Hence Hermite interpolation gives the identity

\[
F(X)=\sum_{i=1}^{M}\sum_{j=0}^{t}F^{[j]}(a_i)H_{ij}(X).
\tag{I}
\]

It remains to show \(H_{ij}(x)\in\mathbb Z_{(p)}\) for every
integer \(x\). This is immediate at a center. Otherwise let \(a_k\)
be the unique representative congruent to \(x\bmod p^N\), and put
\(u=v_p(x-a_k)\ge N\).

The multiset of valuations of \(a_i-a_\ell\), \(\ell\ne i\),
depends only on the complete residue system, and every such valuation is
at most \(N-1\). It follows that

\[
v_p(L_k(x))=0,\qquad
v_p(L_i(x))=u-r\quad(i\ne k),
\qquad r=v_p(x-a_i)=v_p(a_k-a_i)<N.
\tag{V}
\]

For clarity, the second identity follows by cancelling the equal total
valuation of the products indexed by all representatives except their
respective congruent representative. That common total is
\(\sum_{h=1}^{N-1}(p^{N-h}-1)\).

Write \(T_{ij}(Z)=\sum_s b_sZ^s\). The expansion

\[
L_i(a_i+Z)^{-(t+1)}
=\prod_{\ell\ne i}
\left(1+\frac{Z}{a_i-a_\ell}\right)^{-(t+1)}
\]

has integral generalized binomial coefficients. Therefore
\(v_p(b_s)\ge-s(N-1)\).

If \(i=k\), every evaluated term of \(H_{ij}(x)\) has valuation at
least \(ju+s(u-N+1)\ge0\). If \(i\ne k\), (V) gives the lower
bound

\[
(t+1)(N-r)+jr+s(r-N+1).
\]

Since \(0\le s\le t-j\) and \(r\le N-1\), this is at least

\[
N-r+t+j(N-1)>0.
\]

Thus every \(H_{ij}(x)\) is \(p\)-integral, and (I) proves (H).

### Consequence for the moving-degree loophole

For degree \(D\), it is enough to have jets through
\(t=\lfloor D/p^N\rfloor\). Consequently, for fixed \(N\) and any
\(\theta>p^{-N}\), a jet packet containing all orders \(j<\theta D\)
already contains the needed packet for every \(D>0\). A common divisor
of that packet at every allowed deleted-digit prefix cannot produce a
new \(p\)-part beyond the fixed divisor of values on all integers,
even as \(D\) tends to infinity after \(N\) is fixed.

Apply this independently for \(p=2,5\). The primewise representatives
need not be the same. A common power of ten dividing all the relevant
jets at all allowed prefixes then divides every integer value. This
does not exclude point-dependent prime divisibility, a divisor proved
only at the actual pi prefixes, restricted packets missing the required
jets, or a construction with genuinely coupled real-phase information.

Also, (H) is an inequality between a divisor of a jet packet and the
ordinary integer-value fixed divisor. It is not an equality of the
jet-packet fixed divisors on the two sets. For example, derivatives may
have a smaller common divisor than the values even on all integers.

There are joint modular conditions outside this scope. For example,
\(F(X)=5X+6X(X-1)(X-2)(X-3)\) has a factor 2 or 5 at every digit
\(0,\ldots,8\), while \(F(9)\) is coprime to 10. This
point-dependent choice of prime encodes the missing digit, but supplies
no common divisor that can be inserted in the source's determinant bound.

## 4. Where actual pi enters, and the remaining phase requirement

For chosen decimal scales \(n_i\), write
\(p_i=\lfloor10^{n_i}\pi\rfloor\),
\(\rho_i=\{10^{n_i}\pi\}\), \(r_i=2\mathrm i p_i/10^{n_i}\),
and \(\omega=2\pi\mathrm i\). The source's translated row at
period index \(j\) has the exact transverse displacement

\[
\epsilon_i=j(r_i-\omega)
 =-2\mathrm i j\,10^{-n_i}\rho_i.
\]

Actual pi enters the nonlinear row substitution through
\(e^{j\omega}=1\). Avoiding a prescribed decimal cylinder restricts
\(\rho_i\) to its complement. It supplies neither a small enough
uniform approximation exponent nor a sign for the complete sum of
translated determinants. The source bounds the absolute values of
individual translated terms and then adds them; its estimate discards
their relative phases.

To make this route work outside its existing exponent regime, a new input
would have to exploit those phases or different arithmetic. For example,
with the source's row count \(M_H\), normalized row weight
\(\bar b_H\), and arithmetic error \(E_{\rm ar}\), an upper bound

\[
\left|\sum_{\mathcal T}
   \xi_{\mathcal T}\det T_{\mathcal T}\right|
 \le \exp\{-M_HH(1-\bar b_H+E_{\rm ar}+\delta)\},
 \qquad\delta>0,
\]

derived from target avoidance at suitably selected actual-pi scales,
would contradict the source's nonzero Gaussian-integer determinant lower
bound. The sum is the exact pre-modulus translation expansion, including
the logarithmic truncation tails. No such target-dependent estimate is
proved here or furnished by the cited source. This display identifies
the missing input; it is not proposed as a new conjecture or equivalent
consumer. The Hermite lemma does not rule out actual-pi-only divisibility
or a genuinely phase-sensitive construction.

## Reproducible checks

Run from the repository root:

```text
python3 workflows/experiments/openai_math_interpolation_20261017/check.py
```

The checker uses only the Python standard library and contains all its
inputs. It checks rational parameter witnesses, complete prime-power
residue coverage for every deleted digit at small depths, the joint
modular example, 71 Hermite cardinal basis polynomials, 1,049 exact Taylor
coefficients, and 5,396 exact p-integral evaluations. These finite checks
can detect algebraic mistakes; the all-degree and all-precision conclusion
rests on the interpolation proof above.

## Source and scope

The source parameter inequalities and degree-limit order are in
[openai/math family 017, conclusion.tex](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/build/sections/conclusion.tex).
The arithmetic lower bound and Taylor row packets are in
[determinant.tex](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/build/sections/determinant.tex).
Lemma (H) above was independently reviewed, including arbitrary residue
representatives and the boundary cases N=1 and t=0. No claim
is made that it covers every multivariate or phase-sensitive adaptation
of the source.
