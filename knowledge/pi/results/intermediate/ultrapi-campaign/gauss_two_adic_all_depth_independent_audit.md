# Independent audit: Gauss--Lambert all-depth two-adic edge

**Audit date:** 2026-08-12 UTC  
**Claim label:** proof sketch  
**Final post-repair verdict:** **PASS**

The initial source snapshot contained one incorrect displayed logarithmic
primitive. The source author applied the exact repair identified in this
audit, gave it the nonduplicated tag (18a), and strengthened the primary
checker to close two coverage gaps. A narrow inspection and replay of the
repaired snapshots now pass.

This audit establishes only the claimed two-adic valuation formula. It does
not prove the remaining odd-prime estimate, a decimal-cylinder hit, or V1.

## 1. Pinned snapshots and replay

Initial failing snapshots, retained for provenance:

- gauss_two_adic_all_depth_attack.md:
  54c44c910f3617c463a80cf7419d6e3a63eee66c14f08b1bc2d701e23140e567
- gauss_two_adic_all_depth_check.py:
  257b848ee59671c9d1bd285ecf1fa0afa9bedf94d4bbb38207682e39ee9bc56f

Post-repair snapshots independently verified:

- repaired gauss_two_adic_all_depth_attack.md:
  f21983d36a338b0e8dec62c9b12e00da4383833d747869af029496cc24559fb9
- strengthened gauss_two_adic_all_depth_check.py:
  a0bc3fa81bf6ab79be9ac6ec290bc9b78deb65a7aaa19679330de63c6bd2956f
- post-repair gauss_two_adic_all_depth_independent_check.py:
  5507d6ad1f3d89d234f21841b6257f7e7c2cc0370abf7544eb0e220bc8465d85

Both current checkers ran successfully:

~~~text
PASS: exact Q/coefficient normalizations, the mod-4 valuation law through n=512, 2016 odd-shadow isometry pairs, and 17160 paired-term divisibility checks
EXPERIMENT: endpoint partial-sum valuations at N=2^k-1 are 1:2, 3:5, 7:10, 15:19, 31:36, 63:69, 127:134

PASS: independent exact normalization, signed-binomial boundary, 297984 Lipschitz, 2352 factorization, and 38808 high-pair checks
PASS: equation (18) and repaired primitive (18a); the superseded primitive is correctly rejected
EXPERIMENT endpoint: 1:2, 3:5, 7:10, 15:19, 31:36, 63:69, 127:134, 255:263
EXPERIMENT Log(i): 7:1, 15:4, 31:11, 63:26, 127:57, 255:120
~~~

The endpoint rows are explicitly experiment. The proof of the infinite
endpoint identity is the convergence and local-logarithm argument audited
below.

## 2. Applied repair: retain (18), replace the primitive

Put $a=1+i$ and $b=1-i$, so $a+b=ab=2$. The source's crossed partial
fractions are

\[
 \frac{1}{(1-az)(1-bz)}
 =\frac{b/2}{1-az}+\frac{a/2}{1-bz}.                         \tag{A1}
\]

They are correct: after combining the right side, its numerator is

\[
 \frac12\bigl(b(1-bz)+a(1-az)\bigr)
 =1-\frac{a^2+b^2}{2}z=1.
\]

Swapping the numerators instead produces $(1-2z)/(1-2z+2z^2)$. At $z=1$,
for example, the target is $1$ and the swapped expression is $-1$.

The initial snapshot's primitive

\[
 -\frac12\operatorname{Log}(1-az)
 -\frac12\operatorname{Log}(1-bz)
\]

differentiates to $(1-2z)/(1-2z+2z^2)$, not the integrand. The repaired
source now correctly displays

\[
 \boxed{
 \frac{i}{2}\left(
   \operatorname{Log}(1-(1+i)z)
  -\operatorname{Log}(1-(1-i)z)
 \right)}.                                                    \tag{A2}
\]

Indeed, $-b/(2a)=i/2$ and $-a/(2b)=-i/2$. Direct differentiation of (A2)
gives (A1). At $z=0$ both logarithms vanish; at $z=1$ their arguments are
$-i$ and $i$. Their logarithms vanish as verified in Section 5, so the
endpoint value remains zero. The repaired report labels (A2) as (18a);
equation number (19) now occurs only on the binomial Lipschitz estimate.

## 3. Recurrence and coefficient normalizations

Let $U_n=Q_n/n!$ and $f(x)=\sum_{n\ge0}U_nx^n$. Dividing the recurrence by
$(n-1)!$, summing, and using $Q_0=Q_1=1$ gives

\[
 (1-2x-x^2)f'(x)=(1+x)f(x),\qquad f(0)=1.
\]

Hence $f(x)=(1-2x-x^2)^{-1/2}$, confirming (6). Expanding first in powers
of $x^2/(1-2x)$ and then using the central-binomial series gives

\[
 Q_n=\sum_{k=0}^{\lfloor n/2\rfloor}
 \frac{(n!)^2}{2^k(k!)^2(n-2k)!},                            \tag{A3}
\]

confirming (7). Independently, selecting $k$ quadratic, $n-2k$ linear, and
$k$ constant factors in $(1+2X+2X^2)^n$ gives the coefficient summand

\[
 \frac{n!}{k!^2(n-2k)!}\,2^{n-k}.
\]

Multiplication by $n!/2^n$ recovers (A3), proving (8), including $n=0$.

For $n=2m$, reverse $k=m-j$ in (A3). Exact cancellation yields

\[
 Q_{2m}=2^m((2m-1)!!)^2
 \sum_{j=0}^m\frac{j!\binom mj^2}{(2j-1)!!}.                 \tag{A4}
\]

For $n=2m+1$, the same operation gives

\[
 Q_{2m+1}=2^m((2m+1)!!)^2
 \sum_{j=0}^m\frac{j!\binom mj^2}{(2j+1)!!}.                 \tag{A5}
\]

All displayed denominators are odd, so the later congruences are legitimate
in $\mathbb Z_{(2)}\subset\mathbb Z_2$.

## 4. The finite residue classes

Write the sum in (A4) as $K_m$. Terms with $j\ge2$ are even, so

\[
 K_m\equiv1+m^2\pmod2.
\]

Thus $K_m$ is odd for even $m$. For odd $m$, terms with $j\ge4$ have
valuation at least two, while

\[
 K_m\equiv
 1+m^2+2\binom m2^2+2\binom m3^2\pmod4.
\]

For odd $m$, $\binom m2$ and $\binom m3$ have the same parity: when the
first is odd, their ratio $(m-2)/3$ is $1$ modulo two; when the first is
even, both are even. Their contributions cancel modulo four, while
$1+m^2\equiv2\pmod4$. Therefore

\[
 v_2(K_m)=
 \begin{cases}
 0,&m\ \text{even},\\
 1,&m\ \text{odd}.
 \end{cases}
\]

This proves (12). Write the sum in (A5) as $H_m$. For even $m$, only
$j=0,1$ survive modulo two:

\[
 H_m\equiv1+\frac{m^2}{3}\equiv1\pmod2.
\]

This proves (14), including $m=0$.

## 5. Endpoint convergence and $F(-1)=0$

The coefficient satisfies

\[
 c_j=\frac{j!}{(2j+1)!!}
     =\frac{2^j(j!)^2}{(2j+1)!},
 \qquad v_2(c_j)=v_2(j!)\longrightarrow\infty.
\]

For $x\in\mathbb Z_2$, generalized binomial coefficients
$\binom{x}{j}$ lie in $\mathbb Z_2$, so the series defining $F$ converges
uniformly. The beta identity

\[
 c_j=\int_0^1(2z(1-z))^j\,dz
\]

is an equality of rational numbers obtained by coefficientwise
antiderivative evaluation. For $z\in\mathbb Z_2$, one of $z,1-z$ is even,
so $2z(1-z)\in4\mathbb Z_2$. For the stronger coefficientwise statement,
the $j$-th polynomial carries $2^j$; integration divides by exponents no
larger than $2j+1$ and therefore loses at most
$\lfloor\log_2(2j+1)\rfloor$ powers of two. Since

\[
 j-\lfloor\log_2(2j+1)\rfloor\longrightarrow\infty,
\]

the antiderivatives converge in the closed-disk Tate algebra. This justifies
interchanging the series and endpoint evaluation.

Work in $K=\mathbb Q_2(i)$ with $v_2(2)=1$. Both $1+i$ and $1-i$ have
valuation $1/2$. Therefore

\[
 \operatorname{Log}(1+w)
 =\sum_{r\ge1}(-1)^{r+1}\frac{w^r}{r}
\]

converges uniformly after $w=-(1\pm i)z$ on the closed unit disk: the
$r$-th coefficient has valuation at least $r/2-v_2(r)\to\infty$. It may
be differentiated coefficientwise. The local logarithm is a group
homomorphism on $1+\mathfrak m_K$. Since $\pm i$ belong to that group and
have order four,

\[
 4\operatorname{Log}(\pm i)
 =\operatorname{Log}((\pm i)^4)=0.
\]

The additive group of $K$ is torsion-free, hence both logarithms vanish.
The extended Iwasawa logarithm is unnecessary; if mentioned, its restriction
here agrees with this local series. Substitution in (A2) proves $F(-1)=0$.

## 6. Negative binomials and the paired isometry

For all integers $a,b$, including negative ones, formal Vandermonde gives

\[
 \binom ak-\binom bk
 =\sum_{h=1}^k\binom{a-b}{h}\binom b{k-h}.
\]

Generalized integral binomial coefficients remain integers, and

\[
 \binom{a-b}{h}
 =\frac{a-b}{h}\binom{a-b-1}{h-1}.
\]

Every summand therefore has valuation at least
$v_2(a-b)-v_2(h)$, proving the loss of at most
$\lfloor\log_2 k\rfloor$. This explicitly covers upper argument $-1$.

With $x=2t-1$, the identities

\[
 \frac{c_{2r+1}}{c_{2r}}=\frac{2r+1}{4r+3},
 \qquad
 \binom{x}{2r+1}
 =\binom{x}{2r}\frac{x-2r}{2r+1}
\]

give the report's factorization (22) and polynomial (23). Direct expansion
confirms

\[
 M_r(t)-M_r(s)=2(t-s)(t+s-2r-1).
\]

The prefactor in (22) has valuation $1+v_2((2r)!)$. Applying the signed
binomial bound to upper arguments differing by $2(t-s)$ proves (25).
At the first high-pair boundary, $r=2$,

\[
 v_2(4!)=3=\lfloor\log_2 4\rfloor+1.
\]

For $r\ge3$, the $r$ even factors in $(2r)!$ already give
$r\ge\lfloor\log_2(2r)\rfloor+1$. Thus every pair with $r\ge2$ has
valuation at least $v_2(t-s)+3$.

The two low pairs expand to (27)--(28). Their divided differences reduce to

\[
 \frac{\Psi_0(t)-\Psi_0(s)}{4(t-s)}
 \equiv t+s-1\pmod2
\]

and, because $G(X)\equiv X^2+1\pmod2$,

\[
 \frac{G(t)-G(s)}{t-s}\equiv t+s\pmod2.
\]

The second reduction remains valid when $t-s$ is even: the divided
difference is an integer polynomial in $s,t$, so coefficientwise reduction
is legitimate. The two low residues sum to one; after division by $4(t-s)$,
each high pair is even.

The infinite paired sum is also legitimate. Since
$v_2(c_j)=v_2(j!)\to\infty$ and every generalized binomial value here is
2-adically integral, its terms tend uniformly to zero. The ideal of elements
with valuation at least $v_2(t-s)+3$ is closed, so the infinite high-pair
tail preserves the congruence. Consequently

\[
 v_2(F(2t-1)-F(2s-1))=2+v_2(t-s)
\]

for distinct nonnegative integers $s,t$, including $s=0$.

Taking $s=0$, using $F(-1)=0$, and writing odd $m=2t-1$ gives

\[
 v_2(H_m)=2+v_2(t)=1+v_2(m+1).
\]

Together with Sections 3--4, this proves all four classes in (2), including
the boundary values $n=0,1,2,3$.

## 7. Checker audit

The initial primary checker had two real coverage weaknesses:

1. Its report said it checked (9), but the code did not construct $K_m$ or
   directly check the even normalization.
2. Its implementation of (7) used integer floor division without an explicit
   integrality assertion.

Both are repaired in the pinned current checker. Its q_binomial_sum function
now forms the summands with exact Fraction arithmetic and asserts that the
sum is integral. Its k_nonnegative function constructs $K_m$, and the main
replay checks (9) directly through $m=128$.

The independent checker separately:

- checks (2) through $n=600$ and both normalizations through $m=200$;
- exhausts 297,984 binomial-Lipschitz cases with upper arguments from $-48$
  through $48$;
- checks 2,352 pair factorizations, including $t=0$ and upper argument $-1$;
- checks 38,808 high-pair divisibility cases from the sharp boundary $r=2$;
- distinguishes the correct crossed partial fractions, the false swapped
  version, the superseded false primitive, and repaired primitive (18a);
- checks finite shadows of both endpoint limits through 255 terms.

These finite checks falsify sign, normalization, and boundary mistakes; they
are not substituted for the infinite arguments in Sections 5--6.

## 8. Disposition

For the pinned repaired source,

\[
 v_2(Q_n)-\lfloor n/2\rfloor=
 \begin{cases}
 0,&n\equiv0,1\pmod4,\\
 1,&n\equiv2\pmod4,\\
 v_2(n+1),&n\equiv3\pmod4
 \end{cases}
\]

passes this independent audit as a proof sketch. It reduces the two-primary
contribution in the prior exceptional-gcd route to $O(\log n)$. It supplies
no bound for the remaining varying odd-prime root aggregate and must not be
promoted to a proof of V1.
