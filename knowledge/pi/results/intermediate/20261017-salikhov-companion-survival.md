# Exact five-adic survival in reduced modified-Salikhov approximants

Date: 2026-10-17. Labels: `proof sketch` and exact finite polynomial
`experiment`. Source integral and its normalization: `literature-checked`.
No Lean, novelty, decimal occurrence, or V1 claim is made.

## Statement

Use the modified Salikhov integral and normalization from
[Zeilberger–Zudilin, Part II](https://arxiv.org/html/1912.06345v2) and
PI's [local-pair note](20260906-salikhov-mod5-support.md):

\[
I_n=i(-1)^{n+1}\int_{-1-2i}^{-1+2i}
 \frac{5x^{2n}(x^4+6x^2+25)^{2n}}{(25-x^2)^{3n+1}}\,dx
 =a_n+b_n\pi,
\qquad q_n=2^{2-\lfloor5n/2\rfloor}b_n\in\mathbb Z.
\]

For every integer \(k\ge1\), put \(h=5^k\) and
\(N_k=(h+1)/2\). Then the argument below gives

\[
\boxed{
 a_{N_k}\in\mathbb Z_5^\times,\qquad
 a_{N_k}\equiv 1+2(-1)^k\pmod5,
\qquad
 \frac{b_{N_k}}{5^k}\equiv(-1)^k\pmod5,
\qquad
 \frac{q_{N_k}}{5^k}\equiv2^k\pmod5.
}
\]

In particular, if \(-a_{N_k}/b_{N_k}=P_{N_k}/Q_{N_k}\) is reduced
with positive denominator, then

\[
\boxed{v_5(Q_{N_k})=k.}
\]

Thus the forced powers of five in this explicit family survive reduction.
This removes the rational-companion cancellation gap on this family. It
does not provide a prescribed decimal residue or a sign law on the family.

The [odd-seed extension](20261017-salikhov-seed-survival.md) gives an
explicit, bounded-degree criterion for every index
\(n=(t5^k+1)/2\), with \(t\) positive, odd, and prime to five.
It supplies further all-\(k\) families and retains the unresolved
same-index intersection with binary multiplier control.

## 1. A rational integration-by-parts identity

Set \(u=x/5\), and define

\[
H(u)=1+6u^2+25u^4,\qquad
E(u)=1+20u^2+125u^4-50u^6,
\]
\[
W(u)=-211+318u^2-75u^4.
\]

The differential in the integral becomes

\[
\omega_n(u)=
 \frac{u^{2n}H(u)^{2n}}{(1-u^2)^{3n+1}}\,du.
\]

For every \(n\ge1\), put

\[
B_n(u)=\frac{u^{2n-1}H(u)^{2n-1}W(u)}{3(1-u^2)^{3n}},
\qquad
\widetilde\omega_n(u)=
 -\frac{u^{2n-2}H(u)^{2n-2}E(u)W(u)}{3(1-u^2)^{3n+1}}\,du.
\]

There is an exact rational-function identity

\[
\boxed{\omega_n=dB_n+(2n-1)\widetilde\omega_n.}
\tag{1}
\]

It follows by the product rule from the two fixed polynomial identities

\[
E=(H+uH')(1-u^2)+3u^2H,
\qquad
(1-u^2)W'+3uW=3uH.
\tag{2}
\]

These identities hold over \(\mathbb Z[u]\), so (1) has no square-root
branch or analytic continuation hypothesis. At both endpoints
\(u_\pm=(-1\pm2i)/5\), one has \(H(u_\pm)=0\), while
\(1-u_\pm^2\ne0\). Because \(2n-1\ge1\),
\(B_n(u_+)=B_n(u_-)=0\). Consequently

\[
I_n=(2n-1)i(-1)^{n+1}\int_{u_-}^{u_+}\widetilde\omega_n.
\tag{3}
\]

## 2. The new differential preserves the integral coefficient bounds

Write \(\widetilde\omega_n=\widetilde R_n(x)\,dx\). Explicitly,

\[
\widetilde R_n(x)=
-\frac53\frac{x^{2n-2}(x^4+6x^2+25)^{2n-2}
 E_x(x)W_x(x)}{(25-x^2)^{3n+1}},
\]
\[
E_x(x)=625+500x^2+125x^4-2x^6,
\qquad W_x(x)=-5275+318x^2-3x^4.
\tag{4}
\]

Indeed, \(E_x=5^4E(x/5)\) and \(W_x=5^2W(x/5)\).
The numerator of (4) belongs to \(5\mathbb Z_{(5)}[x]\), and the
denominator has leading coefficient \(\pm1\). Polynomial division
therefore shows that its polynomial part belongs to
\(5\mathbb Z_{(5)}[x^2]\), with degree at most \(4n-2\).

At the pole \(u=-1\), set \(w=u+1\). The principal-part coefficients
\(\widetilde C_{n,j}\), for \(0\le j\le3n\), satisfy

\[
\widetilde C_{n,j}=[w^{3n-j}]
-\frac{(w-1)^{2n-2}H(w-1)^{2n-2}E(w-1)W(w-1)}
 {3(2-w)^{3n+1}}.
\tag{5}
\]

Every coefficient in (5) lies in \(\mathbb Z_{(5)}\), since 2 and 3
are five-adic units. Symmetry gives the physical-coordinate partial
fractions

\[
\widetilde R_n(x)=\widetilde P_n(x)+
\sum_{j=0}^{3n}5^j\widetilde C_{n,j}
 \left((5+x)^{-j-1}+(5-x)^{-j-1}\right).
\tag{6}
\]

Termwise integration uses the same endpoint factors as the original
local-pair formula:

\[
E_j=i\left[
 ((2+i)/2)^j-((2-i)/2)^j+
 ((3+i)/4)^j-((3-i)/4)^j\right].
\]

Thus, with \(h=2n-1\), the rational part of (3) is

\[
a_n=h(-1)^{n+1}\sum_{j=1}^{3n}
 \frac{\widetilde C_{n,j}E_j}{j}
 +h\,i(-1)^{n+1}\int_{-1-2i}^{-1+2i}\widetilde P_n(x)\,dx,
\tag{7}
\]

and its logarithmic coefficient is

\[
b_n=h\,\frac{(-1)^n}{2}\widetilde C_{n,0}.
\tag{8}
\]

This also gives, for all \(n\ge1\), the general companion estimate

\[
v_5(a_n)\ge v_5(2n-1)-\lfloor\log_5(4n)\rfloor.
\tag{9}
\]

For (9), all endpoint numerators have five-integral coefficients; the
largest integration denominator is at most \(4n-1\). The polynomial
part has an additional factor five. Equation (8) separately gives
\(v_5(b_n)\ge v_5(2n-1)\).

Now specialize to \(h=5^k\), \(n=N_k\), \(k\ge1\). Since
\(3n<2h\), the only index in (7) with \(v_5(j)=k\) is \(j=h\).
All other principal-part terms vanish modulo five after multiplication
by \(h\). For the polynomial part, integration denominators are at most
\(4n-1=2h+1<5h\); its additional factor five makes the whole contribution
zero modulo five. In particular, \(a_n\) is five-integral.

Frobenius in \(\mathbb F_5[i]\) fixes \(i\) and all four bases in
\(E_j\). Hence
\(E_h\equiv E_1=-3/2\equiv1\pmod5\). Every \(N_k\) is odd, so
(7) reduces to

\[
\boxed{a_{N_k}\equiv\widetilde C_{N_k,5^k}\pmod5.}
\tag{10}
\]

## 3. Three polynomial identities give an all-length certificate

Work over \(\mathbb F_5\). Define

\[
F(w)=(w-1)^2((w-1)^2+1)^2,\quad D(w)=(2-w)^3,
\]
\[
S_0(w)=2-(w-1)^2=1+2w-w^2,
\qquad Q(z,w)=(2-w)(D(w)-zF(w)).
\]

Because \(E\equiv1\) and \(-W/3\equiv2-u^2\pmod5\), (5), with
\(m=n-1\), gives

\[
\widetilde C_{n,2n-1}
 =[z^m w^{m+2}]\frac{S_0(w)}{Q(z,w)},
\qquad
\widetilde C_{n,0}
 =[z^m w^{3m+3}]\frac{S_0(w)}{Q(z,w)}.
\tag{11}
\]

These identities follow simply by expanding
\(1/(D-zF)=\sum_{m\ge0}z^mF^m/D^{m+1}\).
The constant coefficient \(Q(0,0)=16\equiv1\) is a unit.

For a polynomial \(A(w)=\sum a_jw^j\), write
\(\Lambda_bA=\sum_{j\ge0}a_{5j+b}w^j\). Put

\[
K(w)=(2-w)^{10}F(w)^2.
\]

The bivariate section selecting exponents congruent to \((2,b)\)
maps \(S(w)/Q(z,w)\) exactly to

\[
\frac{\Lambda_b(S(w)K(w))}{Q(z,w)}.
\tag{12}
\]

To verify (12), use \(Q(z,w)^5=Q(z^5,w^5)\) in characteristic five.
The coefficient of \(z^2\) in \(Q^4\) is
\((2-w)^4\binom42D^2F^2=(2-w)^{10}F^2\).
There are no other powers congruent to 2 modulo five, since
\(\deg_z Q^4=4\).

Define the two polynomials

\[
S_{\rm odd}=4+4w+4w^2+w^3+4w^4,
\qquad
S_{\rm even}=3+2w+2w^2.
\]

The complete finite certificate consists of these three polynomial
equalities over \(\mathbb F_5\):

\[
\Lambda_4(S_0K)=S_{\rm odd},\qquad
\Lambda_2(S_{\rm odd}K)=S_{\rm even},\qquad
\Lambda_2(S_{\rm even}K)=S_{\rm odd}.
\tag{13}
\]

The accompanying exact checker multiplies the polynomials and verifies
every coefficient in (13). This is not a fit to sampled sequence values:
(12) and (13) imply the coefficient formulas at every length by induction.

For \(m=(5^k-1)/2\), the base-five expansion of \(m\) consists of
\(k\) digits 2. The expansion of \(m+2\) has least significant digit
4, followed by \(k-1\) digits 2. After those \(k\) sections, (11)
therefore gives

\[
\widetilde C_{N_k,5^k}=S_{k\bmod2}(0)
 =\begin{cases}4,&k\text{ odd},\\3,&k\text{ even}.\end{cases}
\tag{14}
\]

For the second coefficient in (11),
\(3m+3=5^k+(m+2)\). The same \(k\) sections leave a terminal
\(w^1\) coefficient at \(z^0\), so

\[
\widetilde C_{N_k,0}
 =[w]\frac{S_{k\bmod2}(w)}{(2-w)^4}
 = [w]S_{k\bmod2}+2S_{k\bmod2}(0)
 =\begin{cases}2,&k\text{ odd},\\3,&k\text{ even}.\end{cases}
\tag{15}
\]

Equations (10) and (14) prove the rational-companion congruence. Equation
(8), the oddness of \(N_k\), and (15) prove
\(b_{N_k}/5^k\equiv(-1)^k\pmod5\).
Finally, \(t_k=\lfloor5N_k/2\rfloor\) satisfies
\(t_1=7\) and \(t_{k+1}=5t_k-3\), hence
\(t_k\equiv k+2\pmod4\). Therefore
\(2^{2-t_k}(-1)^k\equiv2^k\pmod5\), proving the stated multiplier
unit congruence.

## 4. What reduction does, and the remaining target gap

For nonzero rational \(a,b\), if \(-a/b=P/Q\) is reduced with
\(Q>0\), then

\[
v_5(Q)=\max(0,v_5(b)-v_5(a)).
\]

The unit congruences above give \(v_5(a_{N_k})=0\) and
\(v_5(b_{N_k})=k\), proving exact survival \(v_5(Q_{N_k})=k\).

No ordered decimal residue is supplied. The family \(N_k\) is also
too sparse for irrationality of the asymptotic phase alone to imply
equidistribution of \(N_k\theta\). An all-integer or positive-density
sign statement cannot silently be restricted to this family. A V1 route
still requires an actual-pi, prescribed-target statement with control of
the reduced numerator, the full denominator, and the approximation error.
Consequently this is an intermediate arithmetic result, not a newly
admitted V1 candidate or a reopening of an unsigned carrier route.


## Reproduction and independent review

This completes the companion claim in the
[forced-divisor note](20261016-salikhov-forced-divisor.md). Run the
[exact checker](../../../../workflows/experiments/salikhov_forced_divisor_20261016/companion_survival.py):

```sh
python3 workflows/experiments/salikhov_forced_divisor_20261016/companion_survival.py --max-n 1563 --direct 8
```

The [recorded output](../../../../workflows/experiments/salikhov_forced_divisor_20261016/companion_certificate.txt)
contains the complete finite check scope. The checker verifies both fixed
integer polynomial identities, coordinate scaling, and every coefficient
of all three Cartier identities. It independently integrates the transformed
differential by rational partial fractions for n=1 through 8 and compares
both coefficients with the published recurrence. The all-index valuation
bounds are checked through 1563 as finite validation; the separate root-branch
certificate checks the special-index units through k=6, n=7813.

The integration-by-parts proof, physical-coordinate scaling, denominators,
endpoint sign, Frobenius step, section digits, and terminal outputs were
independently reviewed by three readers. One reviewer separately recomputed
all three polynomial equalities without using this checker. This is an
algebraic proof sketch with an exact finite certificate; it is not a Lean
proof or a verified resolution of V1.
