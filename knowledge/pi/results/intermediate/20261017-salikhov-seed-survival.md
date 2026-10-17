# Reduced-denominator survival for arbitrary odd Salikhov seeds

Date: 2026-10-17. Label: `proof sketch`, with exact finite polynomial
`experiment`. This extends the [companion-survival proof](20261017-salikhov-companion-survival.md), using its exact
rational integration-by-parts identity and two Cartier states. It makes no
decimal-occurrence or V1 claim.

## 1. An explicit all-index criterion

Fix any positive odd integer \(t\) coprime to 5. For \(k\ge1\), put

\[
n=\frac{t5^k+1}{2},\qquad
M=\frac{t-1}{2},\qquad
5^c\le\frac{3t}{2}<5^{c+1},\qquad p=5^c,
\qquad \sigma=(-1)^{(t+1)/2+1}.
\]

Here \(c\ge0\). The sign \(\sigma=(-1)^{n+1}\) is independent of
\(k\), since \(5^k\equiv1\pmod4\).

Retain from the companion proof

\[
F(w)=(w-1)^2((w-1)^2+1)^2,
\quad
S_{\rm odd}=4+4w+4w^2+w^3+4w^4,
\quad
S_{\rm even}=3+2w+2w^2.
\]

All the following coefficients and outputs are computed in
\(\mathbb F_5\). For \(\epsilon\in\{\mathrm{odd},\mathrm{even}\}\), define

\[
C_{t,\epsilon}(r)=[w^r]
\frac{S_\epsilon(w)F(w)^M}{(2-w)^{3M+4}},
\qquad C_{t,\epsilon}(r)=0\quad(r<0),
\]
\[
r_0=\frac{3t-1}{2},\qquad
r_u=\frac{3t-2up-1}{2}\quad(u=1,2,3),
\]
\[
A_{t,\epsilon}=
t\sigma\big(C_{t,\epsilon}(r_1)+3C_{t,\epsilon}(r_2)
 +C_{t,\epsilon}(r_3)\big)
 +4t\binom{t-1}{(5p-1)/2},
\]
\[
B_{t,\epsilon}=-\frac{t\sigma}{2}C_{t,\epsilon}(r_0).
\tag{1}
\]

The binomial coefficient is zero if its lower index exceeds its upper index.
Then, for every \(k\ge1\),

\[
\boxed{5^c a_n\in\mathbb Z_5,\qquad
5^c a_n\equiv A_{t,k\bmod2}\pmod5,\qquad
b_n/5^k\in\mathbb Z_5,\qquad
b_n/5^k\equiv B_{t,k\bmod2}\pmod5.}
\tag{2}
\]

Consequently:

* If \(A_{t,k\bmod2}\ne0\), then \(v_5(a_n)=-c\), and the reduced
  denominator of \(-a_n/b_n\) has \(v_5(Q_n)\ge k+c\).
* If also \(B_{t,k\bmod2}\ne0\), then \(v_5(Q_n)=k+c\) exactly.
* If \(A_{t,k\bmod2}\ne0\) and \(B_{t,k\bmod2}=0\), then
  \(v_5(Q_n)\ge k+c+1\).

These conclusions apply to every admissible pair \((t,k)\); the proof
does not require holding \(t\) fixed while \(k\) increases.

## 2. Principal-part contribution

Use the auxiliary differential \(\widetilde R_n\), its principal
coefficients \(\widetilde C_{n,j}\), and polynomial part
\(\widetilde P_n\) from the companion proof. Since
\(3n<5^{k+c+1}\), multiplying its rational-part formula by \(5^c\)
leaves, modulo five, only principal denominators
\(j=u5^{k+c}\) with \(1\le u\le4\).
The endpoint factors satisfy

\[
E_{5^{k+c}u}/u\equiv E_u/u
=1,3,1,0\quad\text{for }u=1,2,3,4.
\tag{3}
\]

The last value is why only three principal coefficients occur in (1).

Set \(m=n-1=M5^k+(5^k-1)/2\). Its lowest \(k\) base-five digits
are all 2. For each surviving principal coefficient,

\[
3n-u5^{k+c}=r_u5^k+(5^k+3)/2.
\]

Thus the lowest \(k\) target digits are 4 followed by \(k-1\) digits
2. The same three Cartier identities as in the companion proof replace
the initial numerator by \(S_{k\bmod2}\). The remaining coefficient is

\[
\widetilde C_{n,u5^{k+c}}
=[z^M w^{r_u}]
 \frac{S_{k\bmod2}(w)}{(2-w)((2-w)^3-zF(w))}
=C_{t,k\bmod2}(r_u).
\tag{4}
\]

For the logarithmic coefficient, the identical argument leaves
\(r_0=(3t-1)/2\) instead. The identity
\(b_n=(2n-1)(-1)^n\widetilde C_{n,0}/2\) proves the formula for
\(B\).

## 3. The polynomial part is essential for some seeds

Polynomial division in \(\mathbb Z_{(5)}[x]\) commutes with reduction
modulo five because the leading coefficient of the denominator is a unit.
Reduce the physical-coordinate formula for \(\widetilde R_n/5\):

\[
x^4+6x^2+25\equiv x^2(1+x^2),\quad
E_x\equiv-2x^6,\quad W_x\equiv3x^2(1-x^2),
\quad 25-x^2\equiv-x^2.
\]

The reduced numerator is divisible by the reduced denominator, giving

\[
\boxed{\widetilde P_n(x)/5
 \equiv2(-1)^{n+1}(1-x^2)(1+x^2)^{2n-2}\pmod5.}
\tag{5}
\]

Its integration denominators are at most
\(4n-1=2t5^k+1<2\cdot5^{k+c+1}\). After multiplication by
\(5^c(2n-1)\), the factor five in the polynomial part leaves only
the possible denominator \(j=5^{k+c+1}\). If this exceeds the degree
bound, the corresponding coefficient below is automatically zero.

Let \(J=(5^{k+c+1}-1)/2\). By Lucas's theorem, the coefficient of
\(x^{2J}\) in \((1-x^2)(1+x^2)^{t5^k-1}\) is

\[
\binom{t5^k-1}{J}-\binom{t5^k-1}{J-1}
\equiv(1-4)\binom{t-1}{(5^{c+1}-1)/2}
\equiv2\binom{t-1}{(5p-1)/2}\pmod5.
\tag{6}
\]

Indeed, the low \(k\) digits of the upper binomial index are all 4.
Those of \(J\) are all 2; those of \(J-1\) are 1 followed by
\(k-1\) digits 2. The factors are
\(\binom42=1\pmod5\) and \(\binom41=4\pmod5\).

For \(\zeta=-1+2i\), the endpoint numerator
\(i(\zeta^{5^{k+c+1}}-\bar\zeta^{5^{k+c+1}})\) is congruent to
\(i(\zeta-\bar\zeta)=-4\equiv1\pmod5\).
Combining (5) and (6), the two signs \((-1)^{n+1}\) cancel and the
polynomial contribution is exactly

\[
4t\binom{t-1}{(5p-1)/2}\pmod5.
\]

This proves the remaining term of (1), the integrality in (2), and all
the reduced-denominator conclusions.

## 4. Explicit families and an efficient exact certificate

The formulas give these all-\(k\) families. Each pair lists odd/even
\(k\) outputs, respectively.

| \(t\) | \(c\) | \(A_{t,\mathrm{odd}},A_{t,\mathrm{even}}\) | \(B_{t,\mathrm{odd}},B_{t,\mathrm{even}}\) | Reduced depth |
|---|---:|---|---|---|
| 1 | 0 | 4, 3 | 4, 1 | \(v_5(Q_n)=k\) |
| 3 | 0 | 4, 2 | 1, 3 | \(v_5(Q_n)=k\) |
| 7 | 1 | 1, 2 | 4, 3 | \(v_5(Q_n)=k+1\) |
| 9 | 1 | 4, 4 | 1, 1 | \(v_5(Q_n)=k+1\) |
| 13 | 1 | 1, 4 | 4, 2 | \(v_5(Q_n)=k+1\) |
| 17 | 2 | 3, 1 | 3, 1 | \(v_5(Q_n)=k+2\) |
| 71 | 2 | 2, 3 | 0, 0 | \(v_5(Q_n)\ge k+3\) |

Every coefficient in (1) can be evaluated using a bounded-degree Cartier
recursion, without constructing \(F^M\) or the rational approximation.
For the base-five digit pair \((a,b)\), \(0\le a,b<5\), the exact
numerator update is

\[
S\longmapsto\Lambda_b\left(S(2-w)^{16-3a}F(w)^a\right).
\tag{7}
\]

This follows from the same identity \(Q^5=Q(z^5,w^5)\) as before and
\((-1)^a\binom4a\equiv1\pmod5\). Polynomial degrees never exceed
six, starting from either displayed state. Reading all digits of \(M,r\)
and returning the final constant coefficient evaluates \(C_{t,\epsilon}(r)\).
The binomial term is evaluated by Lucas's theorem. Thus (1) is an exact
finite certificate for each seed, with a number of fixed-size polynomial
operations proportional to its digit length.

The nonzero condition cannot be discarded: both outputs in (1) are zero
for \(t=27\), for both parities. This does not mean that reduction removes
all powers of five there; it means that this first-precision certificate
does not decide their survival.

## 5. Compatibility with binary multiplier control

For the separately proved odd-index congruence, let
\(n=1+2^L m\), \(L\ge3\), \(m\ge1\), and
\(s_2(3m)\le L-2\). This gives
\(v_2(q_n)=2+s_2(3m)\). If additionally \(5\mid2n-1\), write
\(2n-1=t5^k\), with \(5\nmid t\), and apply (1).

Whenever \(A_{t,k\bmod2}\ne0\), both conclusions apply to the same
reduced approximation: the five-adic denominator has depth at least
\(k+c\), while the known linear two-adic companion bound and the exact
multiplier valuation control its two-adic numerator. This is a precise,
testable joint arithmetic condition.

An unbounded family satisfying the binary digit-sum condition and the
nonzero output in (1) has not been proved here. In particular, neither
fixed seed families nor finitely many admissible indices establish that
intersection. The ordered decimal residue and target-hit gaps remain.


## Reproduction and review

Run the [standard-library checker](../../../../workflows/experiments/salikhov_forced_divisor_20261016/seed_survival.py):

```sh
python3 workflows/experiments/salikhov_forced_divisor_20261016/seed_survival.py --max-n 1200 --max-seed 93
```

The [recorded output](../../../../workflows/experiments/salikhov_forced_divisor_20261016/seed_certificate.txt)
reports all five Cartier kernels, the original three cycle identities,
1,344 comparisons with independent dense coefficient extraction, and the
eight explicit seed certificates including the zero-output seed 27. The
recurrence check covers 86 seed/index pairs with t at most 93 and n at most
1200. Finite comparisons validate implementation and normalization; the
all-index statement is proved by the coefficient, integration, and Lucas
arguments above.

Independent review checked the principal denominator horizon, sign parity,
base-five carries, polynomial quotient, Lucas indices, and the factor 4t.
A separate bounded-degree implementation reproduced every displayed table
entry. The result remains a proof sketch without Lean verification or a
novelty claim.
