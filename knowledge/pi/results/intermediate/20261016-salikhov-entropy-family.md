# Salikhov intersection on a Fibonacci-size arithmetic family

Date: 2026-10-16. Labels: `proof sketch` and exact `experiment`.
No Lean verification or priority claim. This strengthens the population and
sign conclusions of [the binary-intersection note](20261016-salikhov-binary-intersection.md).
It retains the preceding actual-pi asymptotic and two-adic divisibility
arguments. It supplies no decimal target hit and does not reopen a closed
digit route.

## Result

Keep the rational sequences and normalized modulo-five pair of the
[source note](20260906-salikhov-mod5-support.md):
\[
 I_n=a_n+b_n\pi,\quad R_n=-a_n/b_n,\quad
 q_n=2^{2-\lfloor5n/2\rfloor}b_n,\quad
 c_n=2^{2-\lfloor5n/2\rfloor}a_n,
\]
\[
 Z(n)=\bigl(q_n\bmod5,\;5^{\lfloor\log_5(4n)\rfloor}c_n\bmod5\bigr).
\]
Write \(s_2\) for binary digit sum, and define
\[
 \mathcal G=\{2^km:k\ge2,\ m\ge1\text{ odd},\ s_2(3m)\le k\}.
\]
The condition previously used, \(m<2^{k-1}\), is sufficient for membership
but unnecessarily restrictive for counting.

Let
\[
 \phi=\frac{1+\sqrt5}{2},\quad p=\phi^{-2}=\frac{3-\sqrt5}{2},\quad
 \gamma=\log_2\phi=0.6942419136\ldots,
\]
\[
 H(t)=-t\log_2t-(1-t)\log_2(1-t),\qquad
 \beta=\frac{10}{13}H(3/10)=0.6779160763\ldots<\gamma.
\]

The new statements are:

1. \(\#(\mathcal G\cap[1,N])\asymp N^\gamma\).
2. \(\#\{n\in\mathcal G\cap[1,N]:Z(n)\ne(0,0)\}=O(N^\beta)\).
   Thus the zero local class has relative density one, with exceptional
   proportion \(O(N^{-0.0163258372\ldots})\).
3. Put \(\ell_k=\lfloor\phi^2k\rfloor\), \(N_k=2^{k+\ell_k}\), and
   \[
    \mathcal G_k^*=\{2^km: m\text{ odd},\ 0<3m<2^{\ell_k},\ s_2(3m)\le k\}.
   \]
   There is an explicit, computable infinite set of good indices \(k\)
   such that, for each sign \(\sigma\in\{-1,+1\}\),
   \[
    \#\{n\in\mathcal G_k^*:Z(n)=0,\ \sigma(\pi-R_n)>0\}
       \gg \frac{N_k^\gamma}{\sqrt{\log N_k}}.
   \]
   More precisely, for every sufficiently large good \(k\), each sign
   occupies at least \(1/1000\) of \(\mathcal G_k^*\).
   There is no claim of half-sign balance on these thinner blocks.

For every index in \(\mathcal G\), if \(R_n=P_n/Q_n\) is reduced with
\(Q_n>0\), the established arithmetic input gives
\[
 v_2(q_n)=s_2(3m),\qquad Q_n\text{ odd},\qquad
 v_2(P_n)\ge2n-1-\lfloor\log_2n\rfloor-s_2(3m)
             \ge2n-1-2\lfloor\log_2n\rfloor.
\]
Thus both new sign populations retain the same linear numerator precision.

## 1. Counting by binary length plus digit sum

For a positive integer \(r\), let \(\ell(r)\) be its binary length and
\(w(r)=s_2(r)\). Its binary word starts with a one of cost two. Each
subsequent zero has cost one, and each subsequent one has cost two.
Therefore the exact generating function for positive binary words by
cost \(\ell+w\) is
\[
 A(z)=\sum_{r\ge1}z^{\ell(r)+w(r)}=\frac{z^2}{1-z-z^2}.
\]
In particular its coefficients, and its cumulative coefficients, have
order \(\phi^L\) at cost \(L\).

Set \(L=\lfloor\log_2(3N)\rfloor\). For \(n=2^km\in\mathcal G\),
write \(r=3m\). Then \(r\) is odd, \(w(r)\le k\), and
\[
 2^{k+\ell(r)-1}\le 3n\le3N<2^{L+1},\qquad k+\ell(r)\le L+1.
\]
Ignoring the oddness and divisibility-by-three restrictions, every such
pair is counted by a binary word of cost \(\ell+w\), a nonnegative slack
\(k-w\), and a nonnegative unused cost. The coefficient of
\[
 \frac{A(z)}{(1-z)^2}
\]
at degree \(L+1\) is therefore an upper bound. Its order is \(\phi^L\).

For the lower bound, take any positive binary integer \(u\) of cost at
most \(L-5\). Choose the unique \(v\in\{1,3,5\}\) for which
\(r=8u+v\) is divisible by three. Then \(r\) is odd,
\[
 \ell(r)=\ell(u)+3,\qquad w(r)=w(u)+w(v)\le w(u)+2.
\]
Set \(k=w(r)\ge2\), \(m=r/3\), and \(n=2^km\). This belongs to
\(\mathcal G\), and
\[
 3n<2^{k+\ell(r)}\le2^L\le3N.
\]
The map from \(u\) to \(n\) is injective: recover \(k=v_2(n)\), then
\(r=3n/2^k\), then \(u=\lfloor r/8\rfloor\). The source words have
population \(\asymp\phi^L\). This proves the two-sided count.

## 2. Removing nonzero modulo-five classes throughout the family

The preceding intersection note proves, uniformly in positive \(a,d,M\)
with \(5\nmid d\),
\[
 \#\{0\le j<M:Z(a+dj)\ne0\}=O(M^\delta),\quad
 \delta=\log_5\lambda=0.8804553635\ldots,
\]
where \(\lambda\in(4,5)\) solves \(X^3-4X^2-X+2=0\).

Split \(\mathcal G\cap[1,N]\) at
\(K=\lfloor3L/13\rfloor\). For \(k\le K\), use the digit-sum
restriction, even when counting exceptions. All possible \(r=3m\) fit
in \(t=L+1-k\) bits. With the fixed Bernoulli weight \(a=3/10\), each
word of weight at most \(k\) has probability at least
\(a^k(1-a)^{t-k}\). Hence their number is at most
\[
 a^{-k}(1-a)^{-(t-k)}
 = (10/7)^{L+1}(49/30)^k.
\]
Summing this geometric progression for \(k\le K\) gives
\[
 O\!\left((10/7)^L(49/30)^{3L/13}\right)=O(N^\beta).
\]
There is no logarithmic loss from summing the blocks.

For \(k>K\), discard the digit-sum restriction. The numbers
\(2^km\le N\) with odd \(m\) form a progression with step
\(2^{k+1}\), coprime to five, and length at most \(N/2^k\). The uniform
support bound gives a total exceptional count
\[
 O\!\left(\sum_{k>K}(N/2^k)^\delta\right)
   =O(N^{10\delta/13})=O(N^\beta).
\]
For an exact check of the strict exponent comparison, the cubic is
increasing beyond four and has positive value at \(33/8\), so
\(\lambda<33/8\). The integer inequalities
\[
 33^{1000}<5^{881}8^{1000},\qquad
 10^{1000}>2^{881}3^{300}7^{700}
\]
prove \(\delta<881/1000<H(3/10)\).

Finally \(H(a)/(1+a)\) is maximized at
\(a=p=(3-\sqrt5)/2\): differentiating gives the sign of
\(\log((1-a)^2/a)\). The maximum is \(\log_2\phi\), since
\(p=\phi^{-2}\) and \(1-p=\phi^{-1}\).
This also proves \(\beta<\gamma\) without a rounded decimal comparison.

## 3. Seven low-digit choices control both approximation signs

### A finite rotation lemma

If
\[
 t\in[1/8,3/8]\cup[5/8,7/8],
\]
the seven points \(\{jt\}\), \(0\le j\le6\), have largest circular
gap at most \(1/3\). Here is a finite exact proof. Reflection reduces to
\([1/8,3/8]\). The order of the seven points changes only when
\(t=a/b\) with \(1\le b\le6\). Between successive such breakpoints,
every gap is affine in \(t\), so its maximum is attained at an endpoint.
The complete breakpoint table is

| t | largest gap |
|---|---|
| 1/8 | 1/4 |
| 1/6 | 1/6 |
| 1/5 | 1/5 |
| 1/4 | 1/4 |
| 1/3 | 1/3 |
| 3/8 | 1/4 |

Consequently, after any translation of those seven points, one lies within
circle distance \(1/6\) of zero and another within \(1/6\) of one half.
Their cosines are respectively at least \(1/2\) and at most \(-1/2\).

### Infinitely many computable good indices

For any irrational \(x\), infinitely many indices \(k\) have
\[
 \{2^{k+1}x\}\in[1/8,3/8]\cup[5/8,7/8].
\]
Otherwise the late doubling orbit lies in the radius-\(1/8\)
neighborhoods of \(\{0,1/2\}\). Doubling such a point produces a point
within \(1/4\) of zero. If its successor still belongs to those small
neighborhoods, its nearest center must be zero, not one half. Thereafter
the signed errors from zero double at every step while staying bounded
by \(1/8\). They must be zero, contradicting irrationality.

Apply this to \(x=\theta/(2\pi)\), the irrational phase of the existing
actual-pi asymptotic. Let \(\alpha\) be the upper-half-plane root of
\[
 108X^3-2359989X^2+138304X-2048
\]
and \(\zeta=\alpha/\bar\alpha=e^{2i\theta}\). The good-index test is
exactly the strict real-algebraic inequality
\[
 \boxed{(\zeta^{2^k}+\zeta^{-2^k})^2<2.}
\]
Equality would make \(\zeta\) a root of unity and cannot occur. This
specifies an infinite computable set using no pi digits or unknown
connection phase. No bound on gaps between good indices is claimed.

### Reserving six low bits

Fix a large good \(k\), put \(\ell=\ell_k\), and take every integer
\(0\le u<2^{\ell-6}\) with exactly \(k-5\) binary ones. There are
\[
 C_k=\binom{\ell-6}{k-5}
\]
such cores. Choose the unique \(v_0\in\{1,3,5\}\) making
\(64u+v_0\) divisible by three, and let
\[
 r_j=64u+v_0+6j,\quad m_j=r_j/3,\quad n_j=2^km_j,
 \qquad 0\le j\le6.
\]
Every low part is an odd integer at most 41, with at most five ones.
It fits into six bits without carrying into the core. Thus
\[
 m_j\text{ odd},\quad0<r_j<2^\ell,\quad
 s_2(r_j)\le(k-5)+5=k.
\]
All seven indices belong to \(\mathcal G_k^*\). Their phases differ
by \(2^{k+1}\theta\), precisely the step in the good-index test.
The rotation lemma therefore supplies both cosine signs with margin
\(1/2\), for every core and every connection phase \(\varphi\).
Different cores give disjoint sets of indices.

The inherited actual-pi asymptotic is
\[
 \pi-R_n=K_0(\rho/\Lambda)^n
       (\cos(n\theta+\varphi)+O(1/n)),\quad K_0>0.
\]
Since every candidate index is at least \(2^k\), the error is uniformly
smaller than the fixed cosine margin for all large \(k\). Hence each
sign has at least \(C_k\) actual approximants before the local-class
restriction.

All candidate indices lie in the odd-multiplier progression of length
\(O(2^\ell)\). At most \(O(2^{\delta\ell})\) have nonzero local class.
The floor definition gives \(k-p\ell=O(1)\), not only
\(k/\ell\to p\). Consequently Stirling's formula gives the fixed-constant
bounds
\[
 C_k\asymp\frac{2^{\ell H(p)}}{\sqrt\ell}
     \asymp\frac{N_k^\gamma}{\sqrt{\log N_k}},\qquad H(p)>\delta.
\]
Thus only \(o(C_k)\) of either sign can be lost.

For the explicit positive proportion, the entire block is bounded above
by \(B_k=\sum_{j\le k}\binom\ell j\). Standard ratios of successive
binomial coefficients give
\[
 \frac{B_k}{\binom\ell k}\longrightarrow\frac{1-p}{1-2p},\qquad
 \frac{C_k}{\binom\ell k}\longrightarrow p^5(1-p).
\]
After deleting the negligible exceptions, the lower limit of each sign's
fraction in \(\mathcal G_k^*\) is at least
\[
 p^5(1-2p)=0.0019193787\ldots>1/1000.
\]
For a wholly rational comparison, \(3/8<p<2/5\), so
\(p^5(1-2p)>(3/8)^5/5=243/163840>1/1000\).
This proves the stated eventual proportion. This lower bound does not
assert equidistribution or a limit of the actual sign proportions.

## Verification and scope

The [standard-library checker](../../../../workflows/experiments/salikhov_entropy_family_20261016/audit.py)
checks the finite rotation lemma at every order-change breakpoint, the
integer exponent comparisons, the binary-cost/Fibonacci identity, the
injective construction, exact digit-DP counts, and finite modulo-five
censuses. It also evaluates the good-index test with rigorous outward
integer intervals for the algebraic recurrence roots. An optional exact
rational recurrence check certifies actual-pi signs using the existing
integer Machin enclosure, without relying on a predicted asymptotic sign.

```sh
python3 workflows/experiments/salikhov_entropy_family_20261016/audit.py --census-limit 10000000 --sign-max-n 2000
```

The [recorded certificate](../../../../workflows/experiments/salikhov_entropy_family_20261016/certificate.json)
contains these independently checked counts:

| Cutoff N | Weight family G | Earlier interval family F | G with Z=0 |
|---:|---:|---:|---:|
| 1,000 | 67 | 30 | 43 |
| 100,000 | 1,633 | 322 | 1,226 |
| 10,000,000 | 38,631 | 3,267 | 33,266 |

Through \(n=2000\), the exact rational recurrence and integer pi interval
resolve all 104 weight-family members. The 69 zero-class members comprise
34 lower and 35 upper approximants. All local pairs and reduced-numerator
bounds pass. The independent algebraic interval calculation certifies all
good-index decisions through \(k=80\); for example \(k=7,9,11,19,24,29\)
are good. These small-index decisions do not claim the asymptotic lower
proportion has already taken effect.

These finite checks are `experiment`. The infinite counts, good-index
recurrence, and sign argument are the `proof sketch` above, and retain
the existing arithmetic and analytic prerequisites. The growing
two-adic precision concerns the reduced numerator; the identified
five-adic class is still only the zero class modulo five. Ordered decimal
residues and the other denominator factors remain uncontrolled.
Replacing pi by the explicit word-avoider \(4/9\) makes
\(4/9-R_n\) eventually negative, so this actual-pi two-sign input fails
for that replacement. Nevertheless it gives no target digit occurrence.

Sources: the two linked predecessor notes; the published
[Zeilberger–Zudilin integral](https://arxiv.org/html/1912.06345v2) and
[recurrence](https://sites.math.rutgers.edu/~zeilberg/tokhniot/oSALIKHOVpi3.txt).
