# Modified Salikhov local pair: modulo-five support and relative signs

Date: 2026-09-06. Labels: `proof sketch` with an exact finite-state
`experiment`; source facts `literature-checked`. No Lean or novelty claim.
This concerns a coefficient sequence of an exact representation of pi, not
an admitted digit candidate. It does not reopen the positive-period
carry-selection route.

## Source and normalization

[Zeilberger–Zudilin, arXiv:1912.06345v2](https://arxiv.org/html/1912.06345v2),
Part II, define
\[
R_n(x)=\frac{5x^{2n}(x^4+6x^2+25)^{2n}}{(25-x^2)^{3n+1}},\quad
I_n=i(-1)^{n+1}\int_{-1-2i}^{-1+2i}R_n(x)\,dx=a_n+b_n\pi.
\]
In the symmetric partial fractions,
\[
R_n(x)=P_n(x)+\sum_{j=0}^{3n}A_{n,j}
\big((5+x)^{-j-1}+(5-x)^{-j-1}\big),
\]
the logarithmic term gives \(b_n=(-1)^nA_{n,0}/2\). Their coefficient
divisibility lemma implies
\(q_n=2^{2-\lfloor5n/2\rfloor}b_n\in\mathbb Z\).
For example \(I_0=\pi/4\) and \(I_1=1196\pi-11272/3\).

## Coefficient extraction and exact count

`proof sketch`. Substitute \(x=5(w-1)\), and write
\(H(w)=25(w-1)^4+6(w-1)^2+1\). Comparing Laurent coefficients gives
\[
\frac{A_{n,j}}{5^j}=[w^{3n-j}]
\frac{(w-1)^{2n}H(w)^{2n}}{(2-w)^{3n+1}}.
\]
Set \(F=(w-1)^2H^2\), \(D=(2-w)^3\), \(S_0=(2-w)^2\).
Then \(A_{n,0}\) is the coefficient of \(z^nw^{3n}\) in
\(S_0/(D-zF)\). The denominator is a unit at the origin modulo 5.
The factor relating \(q_n\) to \(A_{n,0}\) is a 5-adic unit, so their
nonzero supports modulo 5 agree.

For \(h_L=\#\{0\le n<5^L:5\nmid q_n\}\), the exact count is
\[
\boxed{\sum_{L\ge0}h_Lz^L=
\frac{1-z-z^2}{1-5z+3z^2+3z^3-2z^4}.}
\]
Equivalently,
\[
h_{L+3}=4h_{L+2}+h_{L+1}-2h_L-1,\quad(h_0,h_1,h_2)=(1,4,16).
\]
The first counts are 1,4,16,65,267,1100,4536,18709,77171.
Thus \(h_L\asymp\lambda^L\), where \(\lambda\approx4.1248854197\)
is the largest root of \(X^3-4X^2-X+2\). In particular \(h_L/5^L\to0\).

### Why the finite certificate implies an all-length count

Over \(\mathbb F_5\), use \((D-zF)^{-1}=(D-zF)^4/(D-zF)^5\).
All coefficients \((-1)^a\binom4a\), \(0\le a<5\), are 1 modulo 5.
A state is a polynomial numerator \(S(w)\) and the carry from computing
\(3n\) in base 5. For an input digit \(a\), the corresponding output
digit is \(b=(3a+\mathrm{carry})\bmod5\); apply the section taking
coefficients numbered \(b\bmod5\) to \(SF^aD^{4-a}\), and update the carry
to \(\lfloor(3a+\mathrm{carry})/5\rfloor\). After the input ends, drain
the carry with zero input digits and evaluate the constant coefficient
divided by \(D(0)\).

Exhausting reachable states gives exactly 27. If \(M\) is their digit
transition matrix and \(v_0\) their nonzero-output indicator, the checker
verifies the **componentwise** identity
\[
(M^4-5M^3+3M^2+3M-2I)v_0=0.
\]
Multiplication by every \(M^L\) proves the homogeneous recurrence at all
lengths. The initial values give the displayed generating function and
inhomogeneous recurrence. This is not an extrapolation from sampled counts.
The starting nonzero state has distinct one-digit loops labeled 0 and 1;
this does not establish branching for the full coefficient pair.

## Reproduction

Run the [standard-library exact checker](../../../../workflows/experiments/salikhov_mod5_support_20260906/check.py):

```sh
python3 workflows/experiments/salikhov_mod5_support_20260906/check.py
```

Independent reproduction verified the exhaustive state construction and
vector identity. Independent direct coefficient extraction also agrees for
\(n=0,\ldots,50\). That latter comparison is finite; the preceding state
argument is what supplies the all-length count. Labels remain `proof sketch`
and `experiment`, not `machine-checked`.

## Irrational phase

The same source gives the characteristic polynomial
\(\chi(X)=108X^3-2359989X^2+138304X-2048\), with one large positive root
and two small conjugate roots \(\alpha,\bar\alpha\). Exact algebra gives
\(\operatorname{disc}\chi=-57(4475640000)^2\); the cubic is irreducible
modulo 11. Its splitting field is therefore an \(S_3\)-extension with
unique quadratic subfield \(\mathbb Q(\sqrt{-57})\). Its only roots of
unity are \(\pm1\): any cyclotomic subfield would be an abelian Galois
subextension. Since \(\alpha/\bar\alpha\ne\pm1\),
\(\arg(\alpha)/\pi\notin\mathbb Q\). This is a `proof sketch` of phase
nonresonance, **not** a signed asymptotic formula by itself.

## Full rational companion and local pair

The following extension is a `proof sketch`, with an independently reproduced
exact finite-state `experiment`. It is not Lean `machine-checked`, and no
novelty is claimed. Put \(t_n=\lfloor5n/2\rfloor\),
\(c_n=2^{2-t_n}a_n\), \(s_n=\lfloor\log_5(4n)\rfloor\) for \(n\ge1\),
and \(Z(n)=(q_n\bmod5,5^{s_n}c_n\bmod5)\).

Write \(C_{n,j}=A_{n,j}/5^j\), zero outside \(0\le j\le3n\), and
\[
D_{n,k}=[y^k]\frac{(1+6y+25y^2)^{2n}}{(1-25y)^{3n+1}},\qquad
\zeta=-1+2i,
\]
\[
E_j=i\left[((2+i)/2)^j-((2-i)/2)^j
             +((3+i)/4)^j-((3-i)/4)^j\right],\quad
J_j=i(\zeta^j-\bar\zeta^j).
\]
The polynomial part at infinity is
\(P_n(x)=5(-1)^{n+1}\sum_{k=0}^{2n-1}D_{n,k}x^{4n-2-2k}\).
Integrating the partial fractions and polynomial part gives
\[
a_n=(-1)^{n+1}\sum_{j=1}^{3n}\frac{C_{n,j}E_j}{j}
       +5\sum_{k=0}^{2n-1}\frac{D_{n,k}J_{4n-1-2k}}{4n-1-2k}.
\]
All numerators here have only powers of two as possible denominators.
Thus \(5^{s_n}c_n\in\mathbb Z_5\). After this normalization, terms whose
denominator has smaller 5-adic valuation vanish modulo five, and the
polynomial part vanishes because of its extra factor five. Frobenius in
\(\mathbb F_5[i]\) gives
\(E_{5^s u}/u\equiv1,3,1\pmod5\) for \(u=1,2,3\).
Consequently, with \(\phi_n=(-1)^n2^{1-t_n}\bmod5\),
\[
Z(n)=\left(\phi_n C_{n,0},
 -2\phi_n(C_{n,5^{s_n}}+3C_{n,2\cdot5^{s_n}}+C_{n,3\cdot5^{s_n}})\right)
 \pmod5.
\]

### Exhaustive full-pair certificate

The [full-pair checker](../../../../workflows/experiments/salikhov_mod5_support_20260906/full_pair.py)
contains the complete transition tables and constructs them from coefficient
sections, not a fit to numerical pairs. Read digits least significant first.
The preceding 27-state section system retains its numerator and carry.
For a positive integer with \(L\) digits, compare it with
\((5^L-1)/4=(11\cdots1)_5\): above this threshold \(s_n=L\), otherwise
\(s_n=L-1\). A three-valued comparison flag can be updated as digits arrive.
In the first case the needed shifted coefficients are those of \(S/D\)
at carry minus \(u\). In the second case the leading digit is 1 and its
preceding carry is 0, so they are coefficients of \(SF/D^2\) at \(3-u\).
Retain the last nonzero-digit output so leading-zero padding changes no output.
The factor \(\phi_n\) only needs \(n\bmod8\) and digit-length parity.

Exhaustion gives 713 reachable raw states. The script verifies their outputs
and every outgoing transition against a 145-state compressed system; partition
refinement also certifies minimality. There is one absorbing zero state and
one strongly connected component of 144 nonzero states, of period two,
with cyclic classes of size 72 and directed diameter eight. The exact outputs are
\[
\mathcal Z=\{(0,0)\}\cup
\{(q,v):q\in\mathbb F_5^\times,\ v\ne2q\}.
\]
All sixteen nonzero outputs occur in both cyclic classes.

Let \(S_z(L)=\{1\le n<5^L:Z(n)=z\}\). Perron--Frobenius theory and
the already certified support count give
\[
\#S_z(L)=(c_{z,L\bmod2}+o(1))\lambda^L\quad(z\ne(0,0)),
\qquad c_{z,0},c_{z,1}>0,
\]
whereas \(\#S_{(0,0)}(L)=5^L-h_L\). Both sparse cyclic subsequences
therefore have the population needed for a relative, not absolute, estimate.

## Signed asymptotic for the actual integral

Use the [published recurrence](https://sites.math.rutgers.edu/~zeilberg/tokhniot/oSALIKHOVpi3.txt)
\(\sum_{j=0}^3P_j(n)y_{n+j}=0\). That source uses \(E_n=-I_n/5\),
so its homogeneous recurrence is unchanged, but its initial conditions must
be multiplied by \(-5\). The checker records all four polynomials explicitly.
For \(C(X)=\sum[n^9]P_j(n)X^j\), \(D(X)=\sum[n^8]P_j(n)X^j\), exact algebra gives
\[
C=2237820\chi,\qquad D-\tfrac12XC'=\tfrac{10019}{570}C.
\]
Substitution of \(y_n=X^nn^\beta\) therefore gives \(\beta=-1/2\)
at each of the three simple characteristic roots.

For completeness, equal moduli of the small conjugate roots do not justify
using a distinct-modulus asymptotic theorem. Instead write the companion
system as \(T_0+T_1/n+O(n^{-2})\). Diagonalize \(T_0\), then conjugate
by \(I+K/n\) to remove off-diagonal terms of order \(1/n\); the denominators
are differences of distinct eigenvalues. The displayed identity makes the
remaining diagonal correction \(-T_0/(2n)\). Remove the scalar power
\(n^{-1/2}\). The spectral gap between the large root \(\Lambda\) and the
small pair permits block diagonalization by invariant graphs of size
\(O(n^{-2})\). In the small block, divide by \(\rho=|\alpha|\) and conjugate
the unitary diagonal rotation. The remaining factors are \(I+O(n^{-2})\);
their product converges invertibly with tail \(I+O(n^{-1})\).
This supplies a conjugate oscillatory basis with a controlled error.

More explicitly, write the normalized blocks as
\(x_{n+1}=A_nx_n+B_ny_n\), \(y_{n+1}=C_nx_n+D_ny_n\), where
\(x_n\) is scalar, \(y_n\) has dimension two,
\(A_n=\Lambda+O(n^{-2})\), \(D_n=\operatorname{diag}(\alpha,\bar\alpha)+O(n^{-2})\),
and \(B_n,C_n=O(n^{-2})\). On a sufficiently late tail, the equation
\[
h_n=(A_n-h_{n+1}C_n)^{-1}(h_{n+1}D_n-B_n)
\]
is a contraction on a ball in the norm \(\sup n^2\|h_n\|\), with limiting
contraction factor \(\rho/\Lambda<1\). It constructs the actual small
invariant graph \(x_n=h_ny_n\), not merely a formal expansion. Setting
\(\xi_n=x_n-h_ny_n\) gives the exact triangular system
\[
\xi_{n+1}=(A_n-h_{n+1}C_n)\xi_n,\qquad
y_{n+1}=C_n\xi_n+(D_n+C_nh_n)y_n.
\]
A nonzero \(\xi\) grows like a nonzero constant times \(\Lambda^n\).
On the small graph, conjugation by
\(\operatorname{diag}(\alpha,\bar\alpha)^{n}\) yields the stated
summable perturbation and an invertible limiting product. If the large
component is nonzero instead, the recurrence for \(y_n/\xi_n\) is a
contraction with \(O(n^{-2})\) forcing and gives \(y_n/\xi_n=O(n^{-2})\).
Choosing companion eigenvectors with first coordinate one preserves the
nonzero amplitude when returning to the original scalar sequence.

On the straight integration segment,
\(|x|^2\le5\), \(|x^4+6x^2+25|\le80\), and \(|25-x^2|\ge20\),
so \(|I_n|\le4^n\). This excludes the mode \(\Lambda>10000\).
The solution is nonzero since \(I_0=\pi/4\), and the recurrence is invertible
at every nonnegative index. Hence its small-mode amplitude is nonzero:
\[
I_n=n^{-1/2}\left(A\alpha^n+\bar A\bar\alpha^n+O(\rho^n/n)\right),\quad A\ne0.
\]
The recurrence has signs \(P_0<0,P_1>0,P_2<0,P_3>0\).
Every monomial coefficient of
\(-10000P_2-P_1-10^8P_3\) is strictly positive. Together with
\(b_0=1/4,b_1=1196,b_2=18662336>10000b_1\), induction proves
\(b_n>0\) and \(b_{n+1}>10000b_n\) for \(n\ge1\).
Thus its dominant amplitude is positive. For some \(K>0\) and real \(\varphi\),
\[
\varepsilon_n:=\pi+a_n/b_n
=K(\rho/\Lambda)^n\left(\cos(n\theta+\varphi)+O(1/n)\right),
\qquad \theta=\arg\alpha.
\]
This step uses the actual pi connection constant, not an arbitrary real
substitution into the rational companion.

## Relative phase and sign balance on every allowed class

Let \(A_d\) be the digit matrices restricted to the 144-state nonzero
component, \(A=\sum A_d\), and choose its positive right Perron vector
\(Ah=\lambda h\). Put
\[
N(t)=\lambda^{-1}\operatorname{diag}(h)^{-1}
       \left(\sum_{d=0}^4e^{idt}A_d\right)\operatorname{diag}(h).
\]
Its maximum row-sum norm is at most one. Exhaustive checking finds in
every row two length-two paths to the same endpoint, with numerical digit
value difference 2 (128 rows) or 8 (16 rows). Each path has normalized
weight \(h_j/(\lambda^2h_i)\ge5^{-10}\): the graph diameter is eight and
\(\lambda<5\). Combining those two terms, and using
\(|\sin4t|\le4|\sin t|\), proves
\[
\|N(t)N(5t)\|_\infty\le1-\kappa\sin^2(4t),\qquad
\kappa=(16\cdot5^{10})^{-1}.
\]
Consequently the length-\(L\) product is bounded by
\(\exp[-\kappa\sum_{k<\lfloor L/2\rfloor}\sin^2(4\cdot25^kt)]\).
For irrational \(t/\pi\), this exponent tends to minus infinity.
Indeed, convergence of the nonnegative sum would imply
\(\operatorname{dist}(25^ky,\mathbb Z)\to0\), \(y=4t/\pi\).
For nearest integers \(m_k\), eventually errors are less than \(1/27\),
forcing \(m_{k+1}=25m_k\). The errors then multiply by 25 while remaining
bounded, so are zero, which would make \(y\) rational.

For every nonzero integer \(\ell\) and every nonzero output class this gives
\[
\left|\sum_{n\in S_z(L)}e^{i\ell n\theta}\right|
\le5^8\lambda^L
 \exp\left[-\kappa\sum_{k<\lfloor L/2\rfloor}
                   \sin^2(4\ell25^k\theta)\right]+1
=o(\#S_z(L)).
\]
The factor \(5^8\) bounds the Perron-vector ratio; the extra one removes
the auxiliary index zero. For the zero class, subtract the entire nonzero
support from the full geometric sum; its population is asymptotic to \(5^L\).
Weyl's criterion therefore gives relative phase equidistribution on all
seventeen classes. Excluding a shrinking neighborhood of the two cosine
zeros in the signed asymptotic yields the `proof sketch`
\[
\boxed{\#\{n\in S_z(L):\varepsilon_n>0\}
       =(\tfrac12+o(1))\#S_z(L)\quad\text{for every }z\in\mathcal Z.}
\]
The negative proportion is also one half. No effective uniform rate in
growing modulus is supplied.

### Verification and scope

Run `python3 workflows/experiments/salikhov_mod5_support_20260906/full_pair.py --direct 20 --recurrence 400 --counts 6`.
Independent Luna reproduction passed all exact state, graph, polynomial,
and positivity checks, including an independent graph traversal and collision
enumeration. Formula-versus-recurrence comparisons through 20 and local pairs
through 400 are finite validation, not proofs of the source recurrence or
coefficient formulas. The analytic argument above was inspected separately;
it remains a `proof sketch`, not a formal verification. A subsequent independent
Fable5.1 review found no blocking error in the normalization, signed asymptotic,
nonzero amplitude, irrational phase or relative contraction argument. Its
phrase that the row sums of \(N(t)\) are one must be read as the stochastic
normalization at \(t=0\); for general \(t\), the correct statement is the
norm bound \(\|N(t)\|_\infty\le1\) used above. That review read the
full-pair/sign version before the two-adic extensions below were added.

## Linear-depth two-adic companion divisibility

Further `proof sketch`, with an independently reproduced exact `experiment`:
\[
\boxed{v_2(c_n)\ge r_n:=2n+1-\lfloor\log_2(4n+1)\rfloor
       \qquad(n\ge1).}
\]
This concerns the rational companion itself, not the reduced numerator of
\(-a_n/b_n\). Its precision grows linearly without constructing larger
modulo-five state systems.

Work in \(K=\mathbb Q_2(i)\), normalized by \(v_2(2)=1\). Set
\(\alpha_0=-1-2i\), \(\beta_0=-1+2i\), \(x=\alpha_0+4it\), and
\[
u=\frac{2i}{2-i},\quad v=-\frac{2i}{3+i},\quad
\gamma_n=\frac{5(-1)^n2^{6n}}{(7-i)^{3n+1}}.
\]
Exact factorization of the quartic numerator gives
\[
i(-1)^{n+1}R_n(\alpha_0+4it)\,4i
=\gamma_n t^{2n}(t-1)^{2n}W_n(t),
\]
\[
W_n(t)=\frac{(\alpha_0+4it)^{2n}(-1+2it)^{2n}
                     (-1-2i+2it)^{2n}}
                   {(1+ut)^{3n+1}(1+vt)^{3n+1}}.
\]
Here \(v_2(u)=1\), \(v_2(v)=1/2\), and
\(v_2(\gamma_n)=(9n-1)/2\). The numerator constants are units and
each linear coefficient has valuation at least one. Negative-binomial
expansion therefore gives \(v_2([t^j]W_n)\ge j/2\).
Writing \(t^{2n}(t-1)^{2n}W_n(t)=\sum g_{n,j}t^j\), we obtain
\[
v_2(g_{n,j})\ge\max(0,(j-4n)/2).
\]
Thus the power-series antiderivative converges at \(t=1\); no
measure-theoretic p-adic integral is being invoked.

The logarithmic endpoint ratio in the symmetric partial fractions is
\[
\frac{(5+\beta_0)(5-\alpha_0)}{(5+\alpha_0)(5-\beta_0)}=i.
\]
The two individual ratios belong to \(1+\mathfrak m_K\), where the
p-adic logarithm converges and is additive. Since \(i\) is torsion,
\(\log_2 i=0\). The complex logarithmic contribution produces pi, but
the two-adic logarithmic contribution is zero. The remaining rational
primitive difference is exactly the same \(a_n\), giving
\[
a_n=\gamma_n\sum_{j\ge0}\frac{g_{n,j}}{j+1}.
\]
For every \(j\ge0\),
\[
\max(0,(j-4n)/2)-\log_2(j+1)\ge-\log_2(4n+1).
\]
For \(j>4n\) this follows from monotonicity of the left expression;
for smaller \(j\) it is immediate. Hence
\(v_2(a_n)\ge(9n-1)/2-\log_2(4n+1)\). Multiplying by
\(2^{2-\lfloor5n/2\rfloor}\) and rounding the valuation of the rational
number \(c_n\) up to an integer proves the displayed conservative bound.

Run `python3 workflows/experiments/salikhov_mod5_support_20260906/linear_2adic.py --terms 400 --primitive-orders 6`.
Independent Luna reproduction verifies the exact Gaussian endpoint ratio,
quartic factorization and valuations; finite recurrence tests through 400
pass. Truncated primitives for \(n=1,\ldots,6\) agree with the rational
companion within rigorous omitted-tail bounds. The all-index assertion rests
on the coefficient and convergent-primitive argument, not those finite tests.
No independent expert or formal verification of this extension is claimed.

For the precise remaining cancellation issue, write
\(c_n=N_n/d_n\) and \(-a_n/b_n=P_n/Q_n\) in reduced form, with positive
denominators. The bound makes \(d_n\) odd, but only implies
\[
v_2(P_n)=\max(0,v_2(c_n)-v_2(q_n))
\ge\max(0,r_n-v_2(q_n)).
\]
A useful bound on \(v_2(q_n)\) on an explicit family is supplied next. With
\(v_n=5^{s_n}c_n\), similarly
\(v_5(Q_n)=\max(0,s_n+v_5(q_n)-v_5(v_n))\).
These exact valuation identities show why companion congruences cannot
silently become congruences of the reduced approximation.

## Multiplier cancellation removed on an explicit family

Further `proof sketch`, with independently reproduced exact algebra and
finite `experiment`. Write \(s_2(m)\) for binary digit sum. For every
\(n=2^km\), \(k\ge2\), \(m\ge1\) odd,
\[
\boxed{q_n\equiv\binom n{n/4}\pmod{2^{k+1}}.}
\]
It follows that
\[
s_2(3m)\le k\quad\Longrightarrow\quad v_2(q_n)=s_2(3m).
\]
These are all-index statements derived below, not extrapolations from the
small valuations in the recurrence sample.

### Ramified coefficient proof

Use \(\mathcal O=\mathbb Z_2[\tau]\), \(\tau^2=2\), and substitute
\(w=2\tau z\) in the original coefficient formula. Exactly,
\[
H(2\tau z)=32h(z),\qquad
h(z)=1-7\tau z+39z^2-50\tau z^3+50z^4.
\]
Define
\[
U(z)=\frac{(1-2\tau z)^2h(z)^2}{(1-\tau z)^3}.
\]
For even \(n\), all the powers in the normalization cancel and give
\(q_n=[z^{3n}]U(z)^n/(1-\tau z)\). In the ring
\(\mathcal O/2\mathcal O\), where \(\tau^2=0\),
\[
U(z)\equiv(1+z^4)(1+\tau z)\pmod{2\mathcal O[[z]]}.
\]
This is reduction modulo **2**, not modulo the uniformizer \(\tau\).
If \(A-B\in2\mathcal O[[z]]\) and \(v_2(n)=k\), the binomial expansion
gives \(A^n-B^n\in2^{k+1}\mathcal O[[z]]\), since its \(j\)-th term has
valuation at least \(j+v_2\binom nj\ge j+k-v_2(j)\ge k+1\).

Set \(R=3n/4\), and
\(S_\ell(n)=\sum_{j=0}^{\min(4\ell,n)}\binom nj\).
Applying this lifting and extracting the coefficient gives
\[
q_n\equiv\sum_{\ell=0}^{R}4^\ell S_\ell(n)\binom n{R-\ell}
          \pmod{2^{k+1}}.
\]
The factor \(4^\ell\) comes from \(\tau^{4\ell}\); the partial binomial
sum also includes the denominator \((1-\tau z)^{-1}\).
The \(\ell=0\) term is the required binomial coefficient. For \(k\ge3\),
terms with \(2\ell\ge k+1\) vanish immediately. For every remaining
\(1\le\ell\le\lfloor k/2\rfloor<2^{k-2}\),
\(v_2(R-\ell)=v_2(\ell)\), and
\[
v_2\left(4^\ell\binom n{R-\ell}\right)
\ge2\ell+k-v_2(\ell)\ge k+2.
\]
For \(k=2\), only \(\ell=1\) needs separate treatment:
\((1+x)^{4m}\equiv(1+x^4)^m\pmod2\) with \(m\) odd gives
\(S_1(n)\equiv1+1=0\pmod2\), so this term also vanishes modulo eight.
This proves the congruence. Finally factorial valuations give
\[
v_2\binom n{n/4}=s_2(n/4)+s_2(3n/4)-s_2(n)=s_2(3m).
\]
When this is less than \(k+1\), the congruence determines \(v_2(q_n)\)
exactly.

### A square-root-size family with linearly divisible reduced numerators

Take
\[
\mathcal F=\{2^km:k\ge2,\ m\text{ odd},\ 1\le m<2^{k-1}\}.
\]
Here \(3m<3\cdot2^{k-1}\) implies \(s_2(3m)\le k\).
Each \(k\) supplies \(2^{k-2}\) distinct indices below \(2^{2k-1}\),
and their 2-adic valuations distinguish the different \(k\). Consequently
\(\#(\mathcal F\cap[1,N])\gg\sqrt N\).
For \(-a_n/b_n=P_n/Q_n\) in reduced form, the companion bound now gives
\[
v_2(P_n)\ge2n+1-\lfloor\log_2(4n+1)\rfloor-s_2(3m)>0,
\]
and in particular
\[
\boxed{v_2(P_n)\ge2n-1-2\lfloor\log_2 n\rfloor,\qquad
Q_n\text{ odd}\quad(n\in\mathcal F).}
\]
The equality \(\lfloor\log_2(4n+1)\rfloor=\lfloor\log_2n\rfloor+2\)
holds for positive integral \(n\). Thus cancellation by the multiplier
does not consume the linearly growing precision on this explicit family.
For example \(v_2(q_{2^k})=2\) for every \(k\ge2\). More generally,
\(v_2(q_{2^{b+2}(2^{2j+1}+1)/3})=2\) for all \(b,j\ge0\), because
three times the odd part has exactly two binary ones. This does not assert
bounded valuation on an arithmetic progression.

Run `python3 workflows/experiments/salikhov_mod5_support_20260906/multiplier_cancellation.py --terms 1000 --direct 20`.
Independent Luna reproduction passed the exact ramified polynomial identity,
the direct coefficient comparison through 20, the congruence at every multiple
of four through 1000, and reduced-numerator survival in all 67 admissible
cases (30 from \(\mathcal F\)). Root separately inspected the coefficient
proof and its exceptional \(k=2\) step. The all-index proof is the algebra
above, not the 1000-term loop. No formal or novelty claim is made.

### The new intersection gap

The numerator bound holds at every \(n\in\mathcal F\), whatever its
modulo-five pair or sign. But the previously established relative sign law
does not automatically survive restriction to \(\mathcal F\): this is
not a fixed-periodic restriction, and each fixed \(k\) contributes only
finitely many members. Relative phase cancellation on
\(\mathcal F\cap S_z(L)\), for a population tending to infinity, is a
separate open estimate. Pigeonhole only guarantees one fixed output class
has \(\gg5^{L/2}\) such indices along an unbounded subsequence of lengths;
it neither identifies that class nor guarantees both signs there.
Other odd denominator primes and ordered decimal residues are still not
controlled. No digit conclusion follows from numerator divisibility alone.

## Remaining digit gap

This fixed-modulus signed result does not determine the ordered residues of
\(10^m(-a_n/b_n)\). Growing compatible local precision and the other
denominator primes remain uncontrolled. No E, CW0, CW9, or V1 conclusion
follows from this coefficient-support result.
