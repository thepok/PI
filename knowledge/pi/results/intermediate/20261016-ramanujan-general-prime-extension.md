# Ramanujan defect: proposed extension to every prime greater than three

Date: 2026-10-16. Status: `proof sketch`; not formal verification.

This extends the [September 6 global Frobenius proof sketch](20260906-ramanujan-frobenius-proof-sketch.md)
from the single prime 5 to every prime p>3. It does **not** replace that argument by an
elementary proof, and it does not upgrade its status. The new arithmetic
steps are an integral low-degree argument and a normalization that removes
the cube-root ambiguity also at split primes. The geometric comparison
and its functoriality remain explicit inputs, with their general-prime
hypotheses checked below. No decimal-digit conclusion or priority claim is
made.

## 1. Proposed statement and review boundary

Put

\[
b_N=\binom{2N}{N}^3/256^N,\qquad
S_N=\sum_{j<N}(6j+1)b_j,\qquad
\chi_p=(-1)^{(p-1)/2}.
\]

For every prime p>3 the proposed conclusion is that there is one series

\[
P_p\in-32E_{p-3}+p\mathbb Z_p\langle x\rangle
\]

such that, for **every** positive integer N,

\[
S_{pN}-\chi_p pS_N=p^3N^3b_NP_p(N).                 \tag{1}
\]

Here the Euler-number convention is E_0=1, E_2=-1, E_4=5. In particular,

\[
\frac{256^N}{p^3N^3\binom{2N}{N}^3}
 (S_{pN}-\chi_p pS_N)\equiv-32E_{p-3}\pmod p,       \tag{2}
\]

including cutoffs divisible by p and cutoffs with arbitrarily many
base-p central-binomial carries. The proposed analytic statement also gives

\[
v_p(P_p(M)-P_p(N))\ge1+v_p(M-N).                   \tag{3}
\]

If p does not divide E_{p-3}, (1) would give the exact defect valuation
3+3v_p(N)+3v_p(binomial(2N,N)). No assertion that infinitely many primes
satisfy this extra Euler-number condition is needed or made.

Equation (2) is the corresponding part of Sun's 2019 Conjecture 22(i),
equation (2.15), recorded in the [predecessor defect note](20260906-ramanujan-fiveadic-defect.md). The claimed Tate
interpolation is stronger. The use of the word "proposed" concerns the
retained global comparison proof-sketch boundary, not a claim that a
finite calculation proves (1). Section 7 gives a separate unconditional
restricted-cutoff theorem, and Section 8 states the exact dependency.

## 2. An integral gamma-ratio interpolation, uniformly in p

Let A_p=Z_p<x>. Define

\[
R_p(t)=\prod_{a=1}^{p-1}\frac{pt+a}{a}=1+E_p(t).
\]

The harmonic sums satisfy H_(p-1) in p^2 Z_p and
H_(p-1)^(2) in p Z_p. For completeness, the second follows by summing
inverse squares in F_p^*, and pairing a with p-a proves the first
modulo p^2. Therefore the coefficients of t and t^2 in E_p have
valuation at least three; all its higher coefficients do as well.
Its degree is p-1 and its leading coefficient has valuation p-1.
Consequently E_p belongs to p^3 Z_p[t].

Write S for polynomial summation, normalized by (Sq)(0)=0 and
(Sq)(x+1)-(Sq)(x)=q(x). A polynomial of degree d loses at most
floor(log_p(d+1)) under S: express it in the falling-factorial basis,
then sum each basis term by dividing by its index plus one. Define

\[
\ell_p(x)=\sum_{j\ge1}\frac{(-1)^{j+1}}j
  \big((SE_p^j)(2x)-2(SE_p^j)(x)\big),\qquad
G_p=\exp(\ell_p).                                  \tag{4}
\]

For j>=2 the coefficient valuation of the summand is at least

\[
3j-v_p(j)-\lfloor\log_p((p-1)j+1)\rfloor.           \tag{5}
\]

This tends to infinity. It is at least j+2: use
(p-1)j+1<=p^j and v_p(j)<=j-2 for j>=2.
For j=1, summation of degrees at most p-2 is integral; the only
possible loss of one digit occurs on t^(p-1), whose coefficient has
valuation p-1>=4. Thus the first summand also belongs to p^3 A_p.

Furthermore R_p(-1-t)=R_p(t). Each polynomial SE_p^j is therefore odd,
by uniqueness of the polynomial summation primitive with constant zero.
The combination F(2x)-2F(x) kills its linear term. Hence

\[
\ell_p\in p^3x^3A_p,\qquad G_p-1\in p^3x^3A_p.     \tag{6}
\]

Separating the multiples of p in factorials gives, exactly at positive
integers,

\[
G_p(N)=\binom{2pN}{pN}/\binom{2N}{N}.
\]

The factors ((p-1)!)^N cancel before taking logarithms; thus no
Teichmuller factor has been silently discarded. Set

\[
H_p(x)=G_p(x)^3\exp(-x\log(256^{p-1})).             \tag{7}
\]

Fermat's theorem makes this logarithm meaningful, and H_p(N)=b_(pN)/b_N.

## 3. The low-degree lemma

Set g(x)=6x+1 and

\[
B_p(x)=\sum_{a=0}^{p-1}(6px+6a+1)
 \prod_{j=0}^{a-1}\frac{(2px+2j+1)^3}{32(px+j+1)^3},
\qquad F_p=H_pB_p.                                 \tag{8}
\]

All denominators in this finite product are units in A_p. The raw
block recurrence is

\[
(S_{p(N+1)}-\chi_ppS_{N+1})-(S_{pN}-\chi_ppS_N)
 =b_N(F_p(N)-\chi_ppg(N)).                          \tag{9}
\]

The following coefficientwise bounds are elementary:

* F_p modulo p^2 is represented by a polynomial of degree at most one.
* F_p modulo p^3 is represented by a polynomial of degree at most two.
* F_p modulo p^4 is represented by a polynomial of degree at most three.

Here is the precision argument, including the upper-half terms. For
a<=(p-1)/2 the coefficient of x^d in the a-th summand of B_p is
divisible by p^d. For a>=(p+1)/2 its numerator contains the factor
p^3(2x+1)^3. After that factor is removed, the coefficient of x^d
in the remaining analytic factor is divisible by p^d. Thus degrees
greater than three in these terms vanish modulo p^4; all these terms
vanish modulo p^3.

Modulo p, B_p is the constant S_p. The established prime-length
supercongruence of Mao--Wen, Theorem 1.1,

\[
S_p\equiv\chi_pp-p^3E_{p-3}\pmod{p^4},             \tag{10}
\]

implies B_p in p A_p. Equation (6) consequently shows that the G_p^3
factor in (7) contributes zero modulo p^4. Finally write
lambda_p=-log(256^(p-1)) in p Z_p. The exponential
exp(lambda_p x) modulo p^k has degree at most k-1 for k=2,3,4,
because j-v_p(j!)>=k whenever j>=k and p>3. Multiplication proves
the three bounds. The coefficient of degree zero is always F_p(0)=S_p.

Mao--Wen's result is a prime-length theorem, used only in (10). It is
not being cited as an arbitrary-cutoff theorem:
https://arxiv.org/pdf/1910.00779 , Theorem 1.1.

## 4. Bounded reduction turns exact comparison into p^3 divisibility

For

\[
L(P)=\frac{(2x+1)^3}{32}P(x+1)-x^3P(x)
\]

the leading coefficient on L(x^d) is -3/4, a p-adic unit for p>3.
Descending polynomial reduction therefore has norm at most one, and
completion gives

\[
A_p=L(A_p)\oplus\mathbb Z_p[x]_{\le2}.             \tag{11}
\]

Let q and red denote these bounded quotient and remainder maps. They
commute with reduction modulo p^k. The elementary consequence needed
here is particularly useful: if F in L(A_p) has degree at most two
modulo p^3, then q(F) is zero modulo p^3; hence F itself belongs to
p^3 A_p. If F additionally has degree at most three modulo p^4, then
q(F)/p^3 is constant modulo p.

Thus once the global argument supplies

\[
\operatorname{red}(F_p)=\chi_ppg,                  \tag{12}
\]

the low-degree lemma supplies, without assuming the desired
divisibility,

\[
F_p-\chi_ppg=p^3LP_p,\qquad
P_p\in\mathbb Z_p\langle x\rangle,
\quad P_p\bmod p\text{ is constant}.              \tag{13}
\]

Telescoping (9) from N=0 proves (1) without division through a singular
step. At N=1, b_1=1/32 and S_1=1, so (10) identifies this constant:

\[
P_p(1)=32(S_p-\chi_pp)/p^3\equiv-32E_{p-3}\pmod p.
\]

This is why proving the cohomological eigenvector alone is sufficient;
the integral normalization is not an additional all-cutoff conjecture.

## 5. General-prime global comparison: quantitative checks

The following repeats the predecessor's geometric mechanism with p
explicit. It is recorded to make clear what extends, and what is still
inside the retained proof-sketch boundary.

Let a=1/4,

\[
L_zg=z(x+1/2)^3g(x+1)-x^3g(x),\qquad
M_z=\mathbb Q_p(z)[x]/L_z\mathbb Q_p(z)[x].
\]

The connection is [(theta+x)g], theta=z d/dz, with cyclic equation
theta^3-z(theta+1/2)^3. Put

\[
K_p=G_p^3\exp(-x\log(64^{p-1})),\qquad
Q_j=\left(\frac{(px+1/2)_j}{(px+1)_j}\right)^3,
\quad C_zg=K_p\sum_{j=0}^{p-1}z^jQ_jg(px+j).
\]

The same exact telescoping gives

\[
C_zL_zg=p^3L_{z^p}(K_pg(px)),\qquad
(\theta+px)C_zg=C_z((\theta+x)g).
\]

Use the explicit radii

\[
\rho=p^{1/(100(p-1))},\qquad
\eta=p^{1/(1000p(p-1))}.
\]

Subtracting degree/(100(p-1)) from (5) still tends to infinity;
the j=1 estimate from Section 2 also remains above the exponential
threshold 1/(p-1). The linear logarithm in K_p has valuation at least
one, so K_p is analytic on |x|<=rho with norm at most one.
All Q_j denominators for j<p are units there.

On

\[
W_\eta=\{|z|\le\eta,\ |1-z|\ge\eta^{-1}\}
       =\{\eta^{-1}\le|z-1|\le\eta\}
\]

write kappa_p=(1-z^p)/(1-z)^p. The binomial expansion gives

\[
\|\kappa_p-1\|\le p^{-1}\eta^{2p-1}<1.
\]

For w=z^p, both max(1,|w|) and |1-w|^(-1) are at most eta^p.
Polynomial reduction by L_w therefore costs at most eta^(2p) per
degree. Since eta^(2p)<rho, the columns of C_z converge after reduction
on this connected annulus and on a strict neighborhood of the
complement of 0,1,infinity. This also justifies reducing its
telescoping and connection identities by polynomial approximation.

The same p-independent rational de Rham identities as in the predecessor
identify M with the Kummer twist of the symmetric square of

\[
E_z:\quad v^2=u^3+\frac{16}{3}(z-4)(1-z)u
                  +\frac{128}{27}(z+8)(1-z)^2.
\]

Its discriminant is 2^18 z^2(1-z)^3. For p>3 this gives a smooth proper
elliptic scheme over Z_p[z,z^(-1),(1-z)^(-1)]. The Kummer double cover
is etale. Etesse's Theorem 7 applies for every such p because its
ramification hypothesis is e<=p-1 and here e=1. Tensor products,
symmetric squares and the Kummer summand give the geometric
overconvergent Frobenius object used in the comparison.

The connection's singularities 0,1,infinity are pairwise distinct
modulo p; its exponents have denominator at most two. Irreducibility
follows from the hypergeometric parameters (1/2,1/2,1/2) and (1,1,1),
whose differences are nonintegral, exactly as in the predecessor.
The complex irreducibility statement implies irreducibility over
Q_p(z): any rational invariant subspace uses finitely many constants,
whose characteristic-zero field embeds in C.

For the full-unit-disc hypothesis, z=-1 is fixed by z->z^p and its
closed radius-r subdisk, r<1, maps into radius at most
max(p^(-1)r,r^p)<r. Pull back a normalized small-disc horizontal basis
using C^(-1). The resulting bases agree on overlaps and cover the
open unit disk. Thus this hypothesis is obtained from the explicitly
constructed C and its determinant, independently of comparing it to
geometric Frobenius.

Kedlaya's Lemma 2.3.6 consequently gives one scalar c_p such that
C=c_p Phi^(-1). Here and below this use includes the same
Gauss--Manin/rigid/crystalline comparison and functoriality inputs as
the predecessor. They are not conclusions of the integer checker.

The determinant is normalized at z=0 on W_eta, which is connected:

\[
\det C_z=p^3(1-z)^{3(p-1)/2}\kappa_p(z)^{3/2}.
\]

At zero the reduced map is K_p(x)g(px) modulo x^3, with determinant
p^3. Its determinant divided by the displayed candidate has derivative
zero on the annulus and hence is constant. This also proves
invertibility needed above without using geometric comparison.

Taylor transport is J_(z<-w)[g]=[(w/z)^x g]. At a=1/4 define
T_p=J_(a<-a^p)C_a. Its scalar kernel is H_p, so T_pg=F_p.
Writing d=1-a=3/4, the near-one square-root branch of d^(1-p) is
(3/p)d^(-(p-1)/2). Therefore

\[
\det T_p=(3/p)p^3.
\]

The geometric elliptic Frobenius has determinant p and the Kummer
fiber has character (3/p), so det(Phi_a)=(3/p)p^3 as well. Keeping
the inverse direction and Taylor identifications in the same order,

\[
T_p=c_p\Phi_a^{-1},\qquad c_p^3=p^6.               \tag{14}
\]

Primary inputs (and their exact scopes):

* Etesse, Theorem 7, p. 599, supplies overconvergent Frobenius for
  the abelian scheme, under e<=p-1:
  https://www.numdam.org/article/ASENS_2002_4_35_4_575_0.pdf .
* Kedlaya, Lemma 2.3.6, gives scalar uniqueness under the four
  hypotheses checked above; Propositions 3.1.10--11 give the
  hypergeometric local structure and irreducibility:
  https://arxiv.org/html/1912.13073v3 .
* The predecessor specifies the proper smooth Gauss--Manin/rigid
  comparison through Lazda, Propositions 3.1, 3.2, 3.4, and the
  crystalline functoriality through Bhatt--de Jong, Corollary 3.8:
  https://www.math.unipd.it/~lazda/resources/Papers/Berthelot.pdf and
  https://arxiv.org/abs/1110.5001 .

## 6. CM eigenvalue and removal of the cube-root ambiguity

At a=1/4 the curve is E:v^2=u^3-15u+22. Write omega=du/v,
xi=u du/v and eta_E=xi-omega. In the Kummer-twisted symmetric
square, the class g=6x+1 is r omega eta_E, where r^2=1-a.

The predecessor's explicit degree-three CM endomorphism over
Q_p(s), s^2=-3, acts by s on omega and -s on eta_E. Its kernel
{O,(3,2),(3,-2)} is etale for p>3, so the same good-model extension
and crystalline functoriality apply at all primes under consideration.

Put epsilon_p=(-3/p). If epsilon_p=1, s belongs to Q_p and Frobenius
preserves both CM lines. Their eigenvalues have product p, so its
symmetric-square eigenvalue on omega eta_E is p. If epsilon_p=-1,
the quadratic extension is unramified, Frobenius sends s to -s and
swaps the CM lines. Its determinant p then makes the product of its
two off-diagonal entries -p, which is the symmetric-square eigenvalue
on omega eta_E. Thus in both cases this eigenvalue is epsilon_p p.
Including the Kummer character gives

\[
\Phi_a[g]=(-3/p)(3/p)p[g]=\chi_pp[g].              \tag{15}
\]

Write c_p=zeta_p p^2, zeta_p^3=1. Equations (14)--(15) give

\[
\operatorname{red}(F_p)=\zeta_p\chi_ppg.
\]

For inert p there is no nontrivial cube root of unity in Q_p, but
that shortcut is unnecessary. For every p>3, the degree-one bound
modulo p^2 from Section 3 and the norm-one remainder map imply

\[
\operatorname{red}(F_p)(0)\equiv F_p(0)=S_p\pmod{p^2}.
\]

Using (10), this yields zeta_p chi_p p congruent to chi_p p modulo
p^2, hence zeta_p congruent to one modulo p. A cube root of unity
in 1+p Z_p is one when p>3. Therefore zeta_p=1 even for split
primes, and (12) follows. Sections 3--4 now yield (1)--(3).

## 7. An unconditional infinite-cutoff consequence

There is a separate conclusion that does **not** use Section 5, (12),
or exact remainder vanishing. Let

\[
\mathcal P=\{5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,
61,67,71,73,79,83,89,97\}.
\]

For every p in this finite set and every positive integer N satisfying

\[
p\nmid N\binom{2N}{N},                              \tag{16}
\]

the actual rational normalization in (2) is integral and obeys (2).
There is no upper bound on N in this assertion.

To prove it, Sections 2--3 give valid coefficientwise truncations, and
the accompanying integer calculation proves for each p in P that

\[
H_pB_p-\chi_ppg\equiv-p^3\,32E_{p-3}L(1)
   \pmod{p^4A_p}.                                  \tag{17}
\]

For example, after division by p^3, the four raw coefficients modulo p
are as follows. These are coefficients in ascending order, before
reduction by L.

| p | -32E_(p-3) modulo p | Raw coefficients modulo p |
| --- | --- | --- |
| 5 | 2 | (1,1,2,1) |
| 7 | 1 | (2,5,3,1) |
| 11 | 10 | (1,6,1,9) |
| 13 | 5 | (3,5,10,6) |
| 17 | 16 | (9,3,6,5) |

All higher coefficients vanish at this precision by the proved
truncation bounds, rather than by testing values at finitely many N.
Multiply (17) at x=j by b_j and sum j=0,...,N-1. Every b_j is p-adically
integral; the L(1) term telescopes. Therefore

\[
S_{pN}-\chi_ppS_N
 +32E_{p-3}p^3N^3b_N\in p^4\mathbb Z_p.
\]

Under (16), division by p^3N^3b_N leaves an error in p Z_p, proving
(2). This is an infinite-cutoff theorem from finite coefficient
certificates plus explicit analytic tail bounds. The calculation is
not a Lean certificate and should not be labelled `machine-checked`.

Condition (16) holds exactly when the base-p digits of N are all at
most (p-1)/2 and its final digit is nonzero: doubling such a base-p
expansion has no carries, and the central-binomial valuation counts
those carries. Thus N=p^k+1 supplies an explicit infinite family for
every p in P and every k>=1. Among 1<=N<p^k there are exactly

\[
\frac{p-1}{2}\left(\frac{p+1}{2}\right)^{k-1}
\]

admissible cutoffs. This digit-restricted family is not the all-cutoff
conclusion (1); it makes no assertion for its unbounded-carry
complement without the global comparison.

**Exact valuation corollary.** All 23 certified constants
-32E_(p-3) modulo p are nonzero. Therefore, for every p in P and every
positive N satisfying (16),

\[
v_p\!\left(S_{pN}-\chi_p pS_N\right)=3.             \tag{18}
\]

This corollary uses only the coefficient certificates and the proved
truncation bounds; it is independent of the global comparison.

## 8. What was established in this follow-up

The logarithmic p^3 bound, coefficient-degree bounds, bounded reduction
argument, and cube-root normalization are elementary deductions with
their proofs displayed above. Together they show the following precise
conditional implication: **the geometric comparison specified in
Section 5, with the stated functorial CM identification, implies the
all-prime analytic interpolation (1).** Section 5 checks why the
predecessor's comparison mechanism has no p=5-only obstruction.

The all-cutoff, all-prime conclusion retains `proof sketch` status because that global
comparison has not been replaced by an elementary proof or formally
verified. In particular this follow-up does not resolve the request for
an unconditional elementary proof of the all-cutoff five-adic metric.
It does isolate a stronger arithmetic extension and the normalization
needed at the previously uncovered split primes.

The [general-prime checker](../../../../workflows/experiments/ramanujan_general_prime_20261016/audit.py)
uses only the Python standard library and writes no files. From the
repository root, run
`python3 workflows/experiments/ramanujan_general_prime_20261016/audit.py`.
The completed run used integer arithmetic to check the coefficient identity

\[
H_pB_p-\chi_ppg\equiv-p^3\,32E_{p-3}L(1)\pmod{p^4A_p}
\]

for all 23 primes 5<=p<=97, with analytically justified truncations.
It separately checked 44 actual cutoffs at p=5,7,11,13,17, including
p^2-1 and p^2, by exact central-binomial arithmetic. These finite
checks test the new constants and arithmetic; they do not certify the
global comparison or the unrestricted infinite statement. Section 7
explains the infinite restricted-cutoff conclusion that the same
certificates do prove. The two higher-precision
p=5 certificates produced during the skeptical audit likewise provide
no additional infinite claim.

The closed decimal-digit routes stay closed: none of (1)--(3) supplies
ordered decimal-residue control or the compatible positive real tail
required by the repository's reopening criteria.
