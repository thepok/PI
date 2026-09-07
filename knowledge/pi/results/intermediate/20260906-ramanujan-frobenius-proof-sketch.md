# Ramanujan fivefold defect: proposed exact Frobenius comparison

Date: 2026-09-06. Label: `proof sketch`, independently reviewed with
explicit completions incorporated below. This is not formal verification.
Companion to [the defect note](20260906-ramanujan-fiveadic-defect.md).
The new claim is exact vanishing of its three remainder constants, not another
finite-precision test. The rational identities below have been independently
reproduced; that alone does not verify the global cohomological comparison.
An independent Pro review found no blocking error after the repairs below;
root inspected the argument and Luna checked the primary-reference hypotheses.
The claim remains a reviewed `proof sketch`, not a `verified resolution`. No novelty,
formal verification, or decimal-digit conclusion is claimed.

## Claim and notation

Retain \(b_N=\binom{2N}{N}^3/256^N\),
\(S_N=\sum_{j<N}(6j+1)b_j\), \(D_N=S_{5N}-5S_N\),
\(U_N=D_N/(125N^3b_N)\), and \(A=\mathbb Z_5\langle x\rangle\).
The proposed conclusion is
\[
U_N=P(N)\quad(N\ge1),\qquad P\in12+25A.
\]
It suffices to establish \(T[6x+1]=5[6x+1]\) in the vector-space quotient
\(\mathbb Q_5\langle x\rangle/L(\mathbb Q_5\langle x\rangle)\), where
\(L(P)=((2x+1)^3/32)P(x+1)-x^3P(x)\) and \(T\) is the five-block
transfer defined in the companion note. This is not a quotient ring.

## 1. Explicit horizontal transfer in a parameter family

Write \(\widehat c_n=(1/2)_n^3/(n!)^3\), so \(b_n=\widehat c_n a^n\),
\(a=1/4\). Set
\[
L_zg=z(x+1/2)^3g(x+1)-x^3g(x),\qquad
M_z=\mathbb Q_5(z)[x]/L_z\mathbb Q_5(z)[x].
\]
Polynomial reduction gives rank three, with basis \([1],[x],[x^2]\).
The connection is \(\nabla_\theta[g]=[(\theta+x)g]\),
\(\theta=z\,d/dz\), because \((\theta+x)L_z=L_z(\theta+x)\).
Its cyclic vector satisfies \((\theta^3-z(\theta+1/2)^3)[1]=0\).

Let \(G(x)\) be the analytic interpolation of
\(\binom{10N}{5N}/\binom{2N}{N}\) constructed in the companion note, and put
\[
K(x)=G(x)^3\exp(-x\log(64^4)),\quad
Q_j(x)=\left(\frac{(5x+1/2)_j}{(5x+1)_j}\right)^3,
\]
\[
C_zg=K(x)\sum_{j=0}^4z^jQ_j(x)g(5x+j).
\]
Five-term telescoping and differentiation give
\[
C_zL_zg=125L_{z^5}(K(x)g(5x)),\qquad
(\theta+5x)C_zg=C_z((\theta+x)g).
\]
The endpoint identity is
\(K(x+1)(x+1/2)^3=K(x)Q_5(x)(x+1)^3\).
Thus \(C:M\to\sigma^*M\), \(\sigma(z)=z^5\), is horizontal in the
inverse-Frobenius direction once the analytic reduction is justified.

For \(w/z\in1+5\mathbb Z_5\), Taylor transport is
\(J_{z\leftarrow w}[g]=[(w/z)^xg]\). Indeed,
\(L_z((w/z)^xg)=(w/z)^xL_wg\), and its derivative is the connection
transport equation. At \(w=a^5\),
\[
T=J_{a\leftarrow a^5}C_a,
\qquad (a^4)^xK(x)=G(x)^3\exp(-4x\log256)=H(x).
\]
This fixes the lift and the normalization, rather than identifying unrelated
Frobenius matrices by congruence.

## 2. Global overconvergence and uniqueness

The logarithmic construction uses
\(R(t)=\prod_{j=1}^4(5t+j)/24=1+E(t)\), \(E\in125\mathbb Z_5[t]\),
and polynomial summation \((Sq)(N)=\sum_{j<N}q(j)\):
\[
\log G(x)=\sum_{m\ge1}\frac{(-1)^{m+1}}m
          ((SE^m)(2x)-2(SE^m)(x)).
\]
Its \(m\)-th term has degree at most \(4m+1\) and coefficient valuation
at least \(3m-v_5(m)-\lfloor\log_5(4m+1)\rfloor\). With
\(\rho=5^{1/100}\), subtracting \((4m+1)/100\) preserves convergence
and the exponential convergence threshold. Since \(v_5(\log64^4)=1\),
\(K\) is analytic on \(|x|\le\rho\), of norm at most one. The denominators
of \(Q_j\), \(j\le4\), are units there.

Choose \(\eta=5^{1/2000}\) and the strict neighborhood
\[
V_\eta=\{\eta^{-1}\le|z|\le\eta,\ |1-z|\ge\eta^{-1}\}.
\]
For \(w=z^5\),
\[
\frac{1-z^5}{(1-z)^5}=1+\frac{5z(1-z+z^2)}{(1-z)^4}
\]
is uniformly close to one; hence
\(\max(1,|w|),|1-w|^{-1}\le\eta^5\).
Descending reduction modulo \(L_w\) costs at most \(\eta^{10}\) per
degree, so \(\|\operatorname{red}_{L_w}(x^n)\|\le\eta^{10n}\).
As \(\eta^{10}<\rho\), all three columns of \(C\) converge on this
strict neighborhood. Continuous reduction also annihilates \(L_wF\), by
polynomial approximation in the radius-\(\rho\) algebra, so the telescoping
and connection identities survive reduction. Pass to the interior of a
slightly smaller strict neighborhood when using the open-domain convention.
This is the global overconvergence argument;
local horizontality alone would not justify scalar uniqueness.

The geometric comparison uses the elliptic family
\[
E_z:v^2=u^3+\frac{16}{3}(z-4)(1-z)u
                   +\frac{128}{27}(z+8)(1-z)^2,
\]
whose discriminant is \(2^{18}z^2(1-z)^3\). Write
\(\omega=du/v\), \(\xi=u\,du/v\), and let the Kummer line have symbol
\(r\), \(r^2=1-z\), \(\theta r=-zr/(2(1-z))\).
The direct de Rham reductions are
\[
\theta\omega=-\frac{5z-2}{12(z-1)}\omega-\frac1{16(z-1)}\xi,
\quad
\theta\xi=\frac{z-4}{9}\omega+\frac{5z-2}{12(z-1)}\xi.
\]
For \(h=r\omega^2\), the hypergeometric equation holds and
\(\det(h,\theta h,\theta^2h)=-1/(1024(z-1)^3)\) in the basis
\(r\omega^2,r\omega\xi,r\xi^2\). Thus \([g(x)]\mapsto g(\theta)h\)
identifies \(M\) with \(K\otimes\operatorname{Sym}^2H^1_{\rm dR}(E_z)\).

For an explicit global model, take
\(B=\mathbb Z_5[z,z^{-1},(1-z)^{-1}]\). Its base is smooth, and the
projective Weierstrass model with the displayed unit discriminant and section
at infinity is a smooth proper elliptic, hence abelian, scheme over \(B\).
The 5-adic completions supply the smooth formal base and proper smooth lift.
The map \(z\mapsto z^5\) lifts Frobenius on the completed base, since
\(1-z^5=(1-z)^5\kappa\) is a unit there. The special base is
\(\mathbb P^1_{\mathbb F_5}\setminus\{0,1,\infty\}\), stable under Frobenius;
one may use the projective-line compactification for its frames and tubes.

[Étesse, 2002, Theorem 7, p. 599](https://www.numdam.org/article/ASENS_2002_4_35_4_575_0.pdf)
gives overconvergent Frobenius on the rigid direct images of an abelian scheme
over a smooth separated base when the coefficient DVR has ramification index
\(e\le p-1\). Here \(e=1,p=5\), so it applies over the whole base,
not just the ordinary locus. His Theorem 1 also supports the alternative
prime-to-five level-cover descent. The de Rham/Gauss--Manin realization and
Frobenius comparison are supplied by
[Lazda, Propositions 3.1, 3.2 and 3.4](https://www.math.unipd.it/~lazda/resources/Papers/Berthelot.pdf),
using this proper smooth formal lift and the compatible frames/tubes locally
on the smooth base. The Kummer line is the anti-invariant direct summand of
the finite étale double cover; tensor and symmetric-square operations then
give the required object. These are geometric inputs, not rational-checker
conclusions. [Kedlaya, Example 4.6](https://arxiv.org/html/1606.01321)
also describes the universal elliptic overconvergent object across supersingular fibers.

[Kedlaya, Frobenius structures on hypergeometric equations](https://arxiv.org/html/1912.13073v3),
Lemma 2.3.6, requires triviality on an open unit disc, pairwise distinct
boundary reductions, regular boundary exponents in \(\mathbb Z_{(5)}\),
and irreducibility over \(\mathbb Q_5(z)\). The full-disc condition is
justified below without confusing a small ODE solution disk with a unit disk.
The boundary is \(0,1,\infty\);
the exponents have denominator dividing two. Proposition 3.1.11 gives
irreducibility for parameters \(\alpha=(1/2,1/2,1/2)\),
\(\beta=(1,1,1)\), since no difference is integral. Although the source
states complex irreducibility, any rational invariant subspace over
\(\mathbb Q_5(z)\) uses finitely many constants; embedding their finitely
generated characteristic-zero field into \(\mathbb C\) would contradict
that statement. Passing to the dual cyclic module preserves irreducibility.
Thus, after proving invertibility and the disc condition below, the application gives \(C=c\Phi^{-1}\)
for one scalar \(c\in\mathbb Q_5^\times\). Direction and dual conventions
must be preserved in this application.

## 3. Exact determinant normalization

The cyclic connection has trace \(3z/(2(1-z))\), and
\(C_0g=K(x)g(5x)\bmod x^3\) has determinant 125, since \(K(0)=1\).
With \(\kappa=(1-z^5)/(1-z)^5\), the determinant differential equation gives
\[
\det C_z=125(1-z)^6\kappa(z)^{3/2},
\qquad
\det J_{a\leftarrow w}=((1-a)/(1-w))^{3/2}.
\]
To justify using \(C_0\) for this global normalization, extend the same
column construction to
\[
W_\eta=\{|z|\le\eta,\ |1-z|\ge\eta^{-1}\}
       =\{\eta^{-1}\le|z-1|\le\eta\}.
\]
This geometrically connected annulus contains both 0 and \(V_\eta\).
The estimate \(\|\kappa-1\|\le5^{-1}\eta^7<1\) and the same polynomial
reduction bounds hold there. Hence \(C\), in its cyclic logarithmic frame,
extends analytically to zero on the same domain. Dividing its determinant
by the displayed nonvanishing candidate gives an analytic function with
zero derivative on the annulus, hence a constant; its value at zero fixes
the constant. No residue-disk-to-global extrapolation is needed.

The binomial branches are those near one. This makes \(C\) invertible
on the strict neighborhood. At \(a=1/4,w=a^5\), the two near-one
arguments are \(341/81\) and \(256/341\). The square root of their
product \(256/81\) congruent to one modulo five is **\(-16/9\)**.
Therefore \(\det T=-125\).

The geometric elliptic Frobenius has determinant 5: perfect cup product
identifies \(\bigwedge^2H^1\) with \(H^2\), and Frobenius multiplies the
degree class by five, as follows from pulling back the origin divisor to
\(5O\). The trace and perfect-duality normalizations are compatible with
crystalline cohomology by
[Berthelot, §2.3(i) and Theorem 2.4](https://www.wstein.org/people/berthelo/publis/Poincare_Kunneth.pdf).
The Kummer line on this
fiber has eigenvalue \(-1\), since \(1-a\equiv2\pmod5\) is nonsquare.
Thus \(\det\Phi_a=-125\). From \(T=c\Phi_a^{-1}\),
\(c^3=(-125)^2=25^3\). There is no nontrivial cube root of unity in
\(\mathbb Q_5\), so
\[
T=25\Phi_a^{-1}.
\]

Here \(\Phi_a=\Phi(a)J_{a^5\leftarrow a}\) is the intrinsic fiber
operator, while the raw map is \(\Phi(a):M_{a^5}\to M_a\). This gives
\(T=J_{a\leftarrow a^5}C_a=c\Phi_a^{-1}\) with the indicated order.
The Kummer sign can also be checked explicitly: its lifted Frobenius
coefficient is \((1-z)^2\kappa^{1/2}\); after this Taylor identification
the coefficient is \((3/4)^2(-16/9)=-1\).

For the remaining uniqueness hypothesis, use the open unit disk at \(b=-1\).
For \(r<1\), Frobenius sends its closed radius-\(r\) subdisk into radius
at most \(\max(5^{-1}r,r^5)<r\). Iterates enter a small disk carrying a
horizontal basis. Pull this basis back using the already constructed
horizontal \(C^{-1}\), and normalize at \(b\). Uniqueness of normalized
local solutions makes the resulting bases agree, trivializing the entire
open unit disk. Thus scalar uniqueness above is not circular.

## 4. The actual distinguished class is a CM eigenvector

The fiber is \(E:v^2=u^3-15u+22\). Specializing the connection gives
\((1+6\theta)h=r\omega(\xi-\omega)\).
An explicit isogeny is
\[
X=u+\frac{24}{u-3}+\frac{16}{(u-3)^2},\qquad Y=vX'(u),
\qquad Y^2=X^3-135X-594.
\]
For \(s^2=-3\), scaling \((X,Y)\mapsto(X/s^2,Y/s^3)\) gives a
degree-three endomorphism \(\alpha\) of \(E\). Its differential action is
\[
\alpha^*\omega=s\omega,\qquad
\alpha^*\xi=-s\xi+2s\omega.
\]
For example the second identity follows from
\(X\omega\equiv3\xi-6\omega\) modulo the exact differential
\(-4d(v/(u-3))\). Thus \(\eta=\xi-\omega\) is the other CM eigenvector,
with eigenvalue \(-s\).

The endomorphism acts on the relevant crystalline realization because it
extends over the smooth models. Its kernel is the étale order-three group
\(\{O,(3,2),(3,-2)\}\). More explicitly, writing \(t=u-3\), the projective
map is
\[
[t(t^3+3t^2+24t+16):v(t^3-24t-32):t^3].
\]
At \(t=0\) its middle coordinate is a unit; at \(O\), \(X,Y\) have pole
orders 2 and 3 with unit leading terms. Elsewhere the displayed affine map
is defined. Scaling by \(s\) is by units in the unramified quadratic
integer ring. The functorial proper-smooth comparison in
[Bhatt--de Jong, Corollary 3.8](https://arxiv.org/html/1110.5001v1)
therefore identifies the computed de Rham action with the special-fiber
crystalline action used next.

The quadratic extension \(\mathbb Q_5(s)\) is unramified and its Frobenius
sends \(s\) to \(-s\). Crystalline functoriality
\(\Phi_E\sigma(\alpha^*)=\alpha^*\Phi_E\) forces
\(\Phi_E\omega=c_1\eta\), \(\Phi_E\eta=c_2\omega\).
Since \(\det\Phi_E=5\), \(c_1c_2=-5\). The symmetric-square eigenvalue
on \(\omega\eta\) is therefore \(-5\); the Kummer twist changes it to
\(+5\). This is supersingular CM, not an ordinary unit-root argument.
Consequently the proposed comparison implies
\[
T[6x+1]=25\Phi_a^{-1}[6x+1]=5[6x+1].
\]

## 5. All-cutoff consequences of the reviewed proof sketch

The bounded integral decomposition in the companion note then gives
\(f=LP\), \(P\in12+25A\), with all three remainders exactly zero.
Telescoping the actual recurrence from \(D_0=0\), using
\[
b_N(LP)(N)=(N+1)^3b_{N+1}P(N+1)-N^3b_NP(N),
\]
gives \(D_N=125N^3b_NP(N)\) for every positive cutoff, without dividing
through a singular step. In particular \(P(1)=-16008833/16777216\) is
the actual selected value. The proposed all-cutoff consequences are
\[
v_5(U_M-U_N)\ge2+v_5(M-N)\quad(M\ne N),
\qquad
v_5(D_N)=3+3v_5(N)+3v_5\binom{2N}{N}.
\]
These are not consequences of the precision-20 certificate alone.

## Reproduction and review boundary

Run `python3 workflows/experiments/ramanujan_fiveadic_defect_20260906/structural.py`
(SymPy required). Independent Luna reproduction passed the transfer endpoint
identity, both Gauss--Manin reductions, cyclic equation and determinant,
distinguished class, determinant branch, CM isogeny and differential action,
and exact initial value. The script does **not** establish overconvergent
Frobenius existence, uniqueness hypotheses, comparison functoriality, or
the resulting all-cutoff theorem. The independent Pro review supplied the
connected-annulus normalization, full-unit-disk argument, explicit Kummer
sign and CM model extension now included above, and found no blocking error.
Luna checked the primary-reference hypotheses; root checked their application
to the explicit smooth family and inspected the proof. The separate Fable5.1
review of the earlier analytic partial results subsequently found no blocking
error in the logarithmic interpolation, infinite-tail estimates, bounded
completion or valuation losses. It read the pre-Frobenius version: its
statement that the remainder was still unresolved describes that older
finite-precision argument, not an objection to the exact comparison here.
The exact cohomological comparison was reviewed by the independent Pro, not
by that Fable call.
No promotion to `verified resolution`
or `machine-checked` is made.

Sun's 2019 Conjecture 22(i), equation (2.15), already includes the weaker
arbitrary-cutoff normalization modulo five; see the companion note. Priority
for this stronger analytic regularity remains unestablished. Even a correct
proof here supplies no ordered decimal-residue estimate or disjunctivity proof.
