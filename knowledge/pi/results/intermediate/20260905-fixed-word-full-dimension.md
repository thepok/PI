# Fixed-word full dimension from guarded Parry measures and local Fourier decay

Status: proof sketch. Date: 2026-09-05; explicit-range refinement: 2026-09-06.
The coordinator checked the derivation and primary analytic inputs and
reproduced the finite experiments. Separate independent reviews upheld the
guarded digit construction and the scale-local analytic bridge, including
uniform BA support, complete-cylinder decay, rational slicing and parameter
order. This is not a Lean result, a novelty claim, a universal P1 resolution,
or a claim about pi's digits.

Every fixed decimal word w of length m>=49,
every digit d occurring in w, A={0,...,9}\{d}, every c in A intersect
{1,...,8}, every finite prefix P avoiding w, and every 0<s<d_w admit
kappa>0 with dim_H(C_w intersect I(P) intersect ALA_(A,c) intersect BA(kappa))>s.
Consequently the same intersection with BA has dimension d_w for each such
fixed word and prefix. The explicit threshold 49 is justified below.

The word, its length, prefix and marker stay fixed as s increases to d_w.
The auxiliary measure and kappa may depend on s, but kappa never varies
with digit depth inside any one construction. ALA and its windows are exactly
those in [OPEN_PROBLEMS](../../workstreams/OPEN_PROBLEMS.md).

## Inputs and the change from the preceding argument

The [arbitrary-word note](20260905-sparse-forcing-arbitrary-word.md) establishes
the following estimates for the prefix automaton of w. Let D be its digit
counting matrix, B=10^m, K=D^m/B, and K(t) its uniform block Fourier mask:

$$
K\mathbf1\ge(8/9)\mathbf1,\qquad
\tfrac12 10^{-v}\le (K^2)_{uv}\le10^{-v},\qquad
\sup_t\max_u\sum_{\ell=0}^{B-1}\sum_v|K_{uv}(t+\ell/B)|
\le L_m:=m(m+1)^2(2+m\log10).
\tag{1}
$$

Here m>=2. In particular K^2 is positive and D is primitive. Its Perron
eigenvalue lambda and eigenvector h>0, normalized by h_0=1, satisfy

$$
D h=\lambda h,\quad \lambda\le10,\quad
B/\lambda^m\le9/8,\quad \max h/\min h\le2.
\tag{2}
$$

The last inequality follows by applying the componentwise row comparison
in (1) to h in K^2h=(lambda^m/B)^2 h. Perron word counting and the free
Parry measure give d_w=log(lambda)/log(10).

The old slicing estimate loses delta*alpha/eta in dimension. The present
argument instead uses complete cylinders of a nonlinear auxiliary measure
and conditional digital tails, giving d_w+delta-1-2epsilon. This is a
different bound, not a limit obtained by changing the forbidden word.

## Auxiliary BA measures with scale-local decay

[Bowen, Theorem 1.4 and Remark 1](https://msp.org/gt/2009/13-5/gt-v13-n5-p10-p.pdf)
give free convex-cocompact subgroups of PSL_2(Z) with limit-set dimensions
delta approaching one. The theorem identifies closures of dimension spectra;
it does not prescribe every exact dimension. [Bourgain--Dyatlov, Theorem 2
and Remark 3](https://arxiv.org/pdf/1704.02909) give decay of oscillatory
integrals for their Patterson--Sullivan measures, for bounded C^2 phases
with derivative bounded away from zero on the limit set and bounded C^1
amplitudes. The decay exponent can be chosen increasing with delta.
Fix 0<eta_*<min(eta(1/2),1/4); use only groups with delta>=1/2.
Group-dependent multiplicative constants need not be uniform as delta rises.

For one fixed group, its Schottky cylinders J=gamma(J_b), of length ell,
have gamma' comparable to ell, |gamma''|=O(ell), and mu_0(J) comparable
to ell^delta. Conformality gives the weight
((1+y^2)/(1+gamma(y)^2)*gamma'(y))^delta on the fixed base cylinder J_b.
Normalize the phase and amplitude by

$$
\phi_J(y)=(\gamma(y)-x_J)/\ell,\qquad
g_J(y)=\frac{1}{\mu_0(J)}
\left(\frac{1+y^2}{1+\gamma(y)^2}\gamma'(y)\right)^\delta.
$$

Bounded distortion gives uniform C^2 and C^1 norms and a positive lower
bound for phi_J'. For the amplitude derivative, use gamma''/gamma'=O(1).
Use a fixed smooth cutoff equal to one on J_b and zero on the other base
cylinders; extend the phase off J_b with derivative positive on those
cylinders and with uniform norms. It can be made bounded outside a fixed
compact neighborhood of the limit set. The separating gaps are fixed.
Applying the oscillatory estimate at frequency ell*xi gives

$$
|\widehat{\mu_0|_J}(\xi)|
\le C\mu_0(J)(1+\ell|\xi|)^{-\eta_*}.
\tag{3}
$$

This is for complete cylinders, not arbitrary sharp restrictions. The
geometry, conformality and cylinder masses used here are in the same
source, section 2, especially (2.17)--(2.18), (2.28)--(2.32).
The stopping partition at scale r has disjoint cylinders of lengths
between c_Gamma*r and r. Only O_Gamma(1) meet any interval of length r;
their total measure is O_Gamma(r^delta).

The whole limit set has one uniform BA constant. To check this without
a symbolic continued-fraction assumption, let H be its hyperbolic convex
hull. Compactness of H/Gamma provides compact K whose Gamma-translates
cover H. For z=x+iy in K and any modular transformation gamma,
Im(gamma z)=y/|cz+d|^2<=max(y,1/y). Thus Im(gamma z)<=Y uniformly for
z in H and every modular gamma. This excludes infinity and rational limit
points. Choose two distinct limit points: each xi is distance at least D>0
from one of them, zeta. If epsilon=|xi-p/q|<=D/4, the semicircle xi,zeta
has a point z of height epsilon with |Re(z)-xi|<=epsilon. Applying a modular
matrix with bottom row (q,-p) yields Y>=1/(5q^2 epsilon). For larger
epsilon use D/4. Hence the limit set lies in BA(kappa_0), where
kappa_0=min(D/4,1/(5Y))>0.

A rational affine map T(x)=(x+b)/R places the compact set and base cylinders
inside (0,1). Its image lies in BA(kappa_0/R), by applying the original
bound to Rp/q-b. Let mu=T_*mu_0. Equation (3), stopping partitions and
dimension survive this fixed change. We have delta-dimensional measures
with delta approaching one, each supported in one BA(kappa_mu), and a
common positive exponent eta_* in their scale-local Fourier estimates.

## Guards and the nonstationary Parry construction

Choose beta in A intersect {1,...,8} excluding both the first and last
digits of w. Such a beta exists. A beta digit cannot complete w from any
state. After beta^m the automaton state is zero because no nonempty prefix
of w starts with beta. One beta alone need not reset the state.

Force the initial word P beta^m. For every sufficiently large k, prescribe
the packet concatenating all uc, u in A^k, in a fixed order. Its first digit
is at position 10^k+2 and its length is ell_k=(k+1)9^k. Immediately before
each packet prescribe a beta^m guard. Choose k_0 large enough to separate
these blocks and the initial prefix, and to have ell_k<=10^k thereafter.
Each occurrence then starts after
n=10^k+1+i(k+1) in J_k, 0<=i<9^k. Neither the window nor ALA is weakened.

Guards are legal from every incoming state and reset before the packet.
Each packet omits d, so it cannot contain w starting from state zero.
Free gaps can be filled with beta. Thus these prescriptions are compatible.
For their fixed position set F, f(N)=|F intersect [1,N]| satisfies, when
10^K<=N<10^(K+1), f(N)<=C_(P,m,k_0)+C(K+1)9^K+m(K+2)=o(N).
The final term includes the possible guard for packet K+1 when its first
digits precede 10^(K+1), even though that packet itself has not begun.

At free positions give an allowed digit transition u -> v probability
h_v/(lambda h_u). At forced positions output the prescribed digit with
probability one on legal rows and zero on impossible rows. Every actually
reachable row sums to one, by the guard construction and admissibility
of the deterministic prefix. There is no conditioning on future survival.
Run to horizon nm and append an independent uniform decimal tail:
nu_n=g_n dx. Let Omega denote the infinite constrained language.
Its images avoid w, begin with P, and satisfy the frozen ALA condition.
Infinitely many markers in {1,...,8} remove decimal endpoint ambiguity.

## Two uniform digital estimates

Every allowed free transition has probability at least 1/20 by (2).
Replacing forced edges in a path by free probabilities gives

$$
\nu_n(D_b)\le 2\lambda^{-N}20^{f(N)}
\le C_\epsilon 10^{-N(d_w-\epsilon)}
\tag{4}
$$

for every depth-N decimal cell, uniformly in n and N. For N>nm, the extra
uniform digits only improve this bound since lambda<=10.

Condition on any positive-mass prefix b of depth N in m*N_0, and let
tau_(n,b)=G_(n,b) dx be its rescaled tail measure. If N>=nm it is Lebesgue.
A free m-block has mask
M(t)=(B/lambda^m) diag(h)^(-1) K(t) diag(h), hence shifted row-l1 bound
at most (9/4)L_m<=D_m:=20m^4. A block touching F has bound B, since its
kernel is substochastic. Beyond the horizon use the uniform scalar mask
times the identity on states.

The row-l1 induction of the predecessor note, starting from the conditioned
state, yields

$$
\sum_{|k|<B^J}|\widehat\tau_{n,b}(k)|
\le2D_m^J B^{f(N+mJ)}.
\tag{5}
$$

Using absolute value after multiplying a truncated row by the all-ones
column would be invalid; the induction keeps the full row norm until the
remaining continuation, whose sup norm is at most one. Counting all forced
positions through N+mJ overcounts the exceptional tail blocks harmlessly.
Put theta_m=log(D_m)/log(B), and fix theta_m<alpha<eta_*.
For every epsilon>0 choose a>0 with ma<epsilon and theta_m+ma<alpha.
Since f(X)<=aX+C_a, (5), rounding T to a B-power, and dyadic summation give

$$
\sum_{|k|\le T}|\widehat\tau_{n,b}(k)|
\le C_\epsilon 10^{\epsilon N}(1+T)^\alpha,\qquad
\sum_k|\widehat\tau_{n,b}(k)|(1+|k|)^{-\eta_*}
\le C_\epsilon 10^{\epsilon N}.
\tag{6}
$$

The constants are uniform in n, N and b. The depth factor is indispensable:
a tail starting with ell forced digits has coefficients bounded below up
to frequencies comparable to 10^ell. Packet lengths are o(their absolute
depth), so (6) absorbs their cost without varying a BA constant.

## Scale-local slicing without a sharp decimal restriction

On the circle define rho_(n,t)=g_n(t-x) mu. For an interval I of length r,
choose N in m*N_0 with r<=h=10^(-N)<Br. Stop the Schottky partition at
scale h and take the cylinders J meeting I. They have lengths comparable
to h and total mass O(h^delta).
The reflected interval t-J meets at most three depth-N decimal cells D_b.
Write p_b=nu_n(D_b), omit zero-mass cells, and extend each nonnegative
G_(n,b) periodically. On J, except at finitely many irrelevant endpoints,

$$
g_n(t-x)\le h^{-1}\sum_{b:\,D_b\cap(t-J)\ne\varnothing}
p_b G_{n,b}(10^N(t-x)).
\tag{7}
$$

Inside its own cell this is the exact density formula, since the integer
cell index disappears under periodic extension. Extra summands are positive.
Pair each summand with the entire cylinder J. Equations (3) and (6) give

$$
\int_JG_{n,b}(10^N(t-x))\,d\mu(x)
\le \sum_k|\widehat\tau_{n,b}(k)|
|\widehat{\mu|_J}(10^Nk)|
\le C_\epsilon\mu(J)10^{\epsilon N}.
\tag{8}
$$

The pairing holds at every t by Fejer approximation: G is a finite step
function, its discontinuities have finitely many preimages, mu is nonatomic,
and the paired series is absolutely summable. No horizon-uniform sup bound
for G or g_n is assumed. In particular mu is never sharply restricted to
the intersecting decimal cell, where (3) would be unavailable.
Combining (4), (7), (8) and summing cylinders gives

$$
\rho_{n,t}(I)\le C_\epsilon |I|^{d_w+\delta-1-2\epsilon},
\tag{9}
$$

uniformly in n and t. Use only positive exponents; larger intervals are
covered by finitely many small ones. Constants may depend on the fixed
word, group, prescribed prefix and epsilon.

## Positive rational slice and parameter order

Taking N=0 in (6) and using global decay of mu gives a uniform tail bound
sum_(|k|>=Q)|nu_n_hat(k) mu_hat(k)|=O(Q^(alpha-eta_*)).
Fix an integer Q large enough to make this less than 1/2. The Q-point
rational grid average of H_n(t)=int g_n(t-x) dmu is then greater than 1/2:
its constant Fourier term is one, and only frequencies in Q*Z survive.
One fixed numerator a has H_(n_j)(a/Q)>=1/2 along an infinite subsequence.
The measures rho_(n_j,a/Q) have uniformly bounded mass and satisfy (9);
a weak limit is nonzero and has the same Frostman bound.

Reflecting by R(x)=a/Q-x modulo one places its support in pi_10(Omega).
Indeed each fixed depth constraint holds eventually, and the corresponding
finite union of closed decimal cylinders is closed; intersect over depths.
The infinitely many markers exclude alternative endpoint codings. Also
R(supp(mu)) lies in BA(kappa_mu/Q^2), by applying the BA inequality at
denominator Qq to any proposed approximation p/q of R(x). Thus the limit
has one positive kappa fixed at all scales.

Choose eta_* once. Since theta_m tends to zero, take m_*>=2 such that
theta_m<eta_*/2 for every m>=m_*. Fix such a word w, P, d and c and set
alpha=eta_*/2. Given 0<s<d_w, choose an actual modular group dimension
delta>max(1/2,1+s-d_w) and epsilon=(d_w+delta-1-s)/4. Equation (9) has
exponent (d_w+delta-1+s)/2>s. The upper bound d_w comes from C_w.
Only delta, epsilon, constants, Q and kappa change when s increases.

## Reproduction and scope

The [guarded Parry experiment](../../../../workflows/experiments/p1prime_guarded_parry_20260905.py)
checks nine overlap patterns, legal multi-digit resets, reachable row masses,
Perron ratios and the free-block conjugation formula. It independently compares
digit-level and block-level characteristic functions after all block depths
and states: 1600 finite comparisons, maximum discrepancy below 1.1e-12.
It also retains a case where one legal beta digit fails to reset the state.
Run with Python 3.10+ and NumPy; it prints results without writing files.
These are experiments, not verification of the infinite argument.

This proof sketch addresses restricted long-word P1-FD and P1-FD-loc, not
all word lengths, arbitrary SFT sparse forcing, or any occurrence in pi.
The argument above originally gave only an existential threshold. The
following independently audited refinement makes it explicit; it supersedes
the older PD-only range for this fixed-word construction, not its proof.

## Explicit range m>=49: uniform-cylinder adaptation (2026-09-06)

Status: proof sketch, with the external inputs literature-checked. The
coordinator checked the primary geometric and oscillatory inputs, every
depth-uniformity step and the parameter order. A separate adversarial review
upheld the adaptation, explicitly checking deletion before reversal,
repeated-cylinder multiplicity, signed matrix lifts and the Frostman constant.
This remains neither Lean nor a novelty claim.

[Lequen--Sahlsten, Theorem 1](https://arxiv.org/html/2607.18010v1)
gives GLOBAL PS Fourier decay with

$$
e(\delta)=\frac{\delta(2\delta-1)}{(2\delta+1)(3-\delta)},
\qquad 1/2<\delta<1.
$$

It does not state the uniform-cylinder conclusion needed here. We derive,
for one fixed Schottky presentation and every complete cylinder J,

$$
|\widehat{\mu_0|_J}(\xi)|
\le C_\Gamma\mu_0(J)(1+|J||\xi|)^{-e(\delta)}.
\tag{10}
$$

All constants below may depend on this fixed group and its dimension, never
on the outer cylinder's depth. The cylinder geometry is in
[Bourgain--Dyatlov, section 2](https://arxiv.org/pdf/1704.02909)
and Lequen--Sahlsten, Lemmas 2.1--2.10; the smoothing and oscillatory inputs
are the latter paper's Lemmas 3.1 and 3.5. No varying-conjugacy theorem or
transfer of decay between equivalent measures is used.

Write J=I_(p b)=gamma_p(I_b), ell=|J| and use the normalized phase Phi_J
and spherical amplitude g_J already defined above. On fixed separated
enlargements U_b of the base intervals, Phi_J' is comparable to 1,
||Phi_J||_(C2)+||g_J||_(C1)<=C_Gamma. Indeed gamma_p''/gamma_p'=-2/(y-q_J),
where q_J=gamma_p^(-1)(infinity) lies in the base interval indexed by the
inverse of the last letter of p, separated from U_b. For empty p the map
is affine and q_J=infinity. Integrating gamma_p' over I_b gives ell;
bounded distortion controls it on U_b. The spherical weight divided by
mu_0(J) is uniformly C1, by the displayed logarithmic-derivative formula
for that weight. Conformality rewrites the normalized cylinder transform as
int_(I_b) exp(-2*pi*i*zeta*Phi_J) g_J dmu_0, where zeta=ell*xi.

Stop the ORIGINAL Schottky coding at length tau, taking words v starting
with b and ending with i. Let v' delete the last letter. Then |I_v| and
|I_v'| are comparable to tau, and there are O(tau^(-delta)) such words.
For Psi_v=Phi_J composed with gamma_(v'), its pole is

$$
q_{p,v}=\gamma_{v'}^{-1}(q_J)\in K_v:=I_{\overline{v'}},
\qquad |K_v|\asymp\tau.
\tag{11}
$$

The bar reverses AND inverts the letters, AFTER deleting the last one.
For v'=b v_2 ... v_(n-1), the first inverse map sends q_J outside I_b
into I_(bar b); the remaining inverse maps give exactly K_v. Thus even
when q_J=infinity, the composed pole is finite and separated from U_i.
The container depends on v, not p. Reversal and parent--child comparison
give its size. Distinct comparable-size cylinders have bounded overlap by
nesting and uniform contraction. Deleting the last letter introduces at
most alphabet-size-minus-one repetitions (none when i is fixed). Hence
cylinder masses and the original Frostman constant give

$$
\#\{v:|q_{p,v}-y|\le\sigma\}
\le C_\Gamma\tau^{-\delta}\sigma^\delta,\qquad \sigma\ge\tau.
\tag{12}
$$

The poles need not lie in the limit set: lower masses are applied to their
containing cylinders, not to balls centered at the poles.

For small tau, gamma_(v')(U_i) is contained in U_b: its enlargement costs
O(tau) around I_v. A determinant-one lift of Psi_v has bottom row
(C_v,D_v)=sqrt(ell)(c_(pv'),d_(pv')). Since Psi_v' is comparable to tau,
|C_v| is comparable to tau^(-1/2), |D_v|=O(tau^(-1/2)). Choose the sign
so L_v(x)=C_v x+D_v>0 on all U_i. Set
S_(u,v)=sqrt(tau)(|C_u-C_v|+|D_u-D_v|). The normalized coefficient family
is bounded and its first coordinate bounded away from zero, so (12) yields
#{v:S_(u,v)<=sigma}<=C tau^(-delta) sigma^delta for sigma>=tau.

The stopped conformal identity gives sums
f_i=sum_v exp(-2*pi*i*zeta*Psi_v) a_v on U_i, with
a_v=w_(v') * (g_J composed with gamma_(v')). The spherical weights give
||a_v||_(C1)<=C tau^delta and, for R=|zeta|>=1,
||f_i'||_infinity<=C(1+R tau). Normalizing C,D by sqrt(tau), the derivative
of each phase difference factors as tau W(x)(A x+B), where W is positive,
comparable to 1 and uniformly C1, and |A|+|B|=S_(u,v).
For one fixed large M, either |A|>=(|A|+|B|)/(2M+1), or |B|>2M|A|.
Lemma 3.5 gives respectively the order-one-half or order-one bound; combining
with the trivial bound and min(1,z^(-1))<=min(1,z^(-1/2)) gives

$$
\left|\int_{U_i}e^{-2\pi i\zeta(\Psi_u-\Psi_v)}
a_u\overline{a_v}\,dx\right|
\le C\tau^{2\delta}\min\{1,(R\tau S_{u,v})^{-1/2}\}.
\tag{13}
$$

At S=0 use the trivial bound. The O(1) near partners S<=tau per u cost
O(tau^delta); dyadic shells above tau cost
C(R tau)^(-1/2) sum_(tau<=sigma<=C) sigma^(delta-1/2).
The sum is bounded because delta>1/2. Therefore
||f_i||_2^2<=C[tau^delta+(R tau)^(-1/2)].

For smoothing, convolve the UNNORMALIZED fixed measure mu_0 restricted to
I_i with the interval kernel of radius r. Its density has L1 norm <=1 and
Linfinity norm <=C F_Gamma r^(delta-1), with the original fixed Frostman
constant F_Gamma. Cauchy--Schwarz and the C1 averaging error yield

$$
\int_{I_i}|f_i|\,d\mu_0
\le C F_\Gamma^{1/2}r^{(\delta-1)/2}\|f_i\|_2
+r\|f_i'\|_\infty.
\tag{14}
$$

There is no division by mu_0(J) in this Frostman constant. Choose
tau=R^(-1/(2delta+1)) and r=R^(-5delta/((3-delta)(2delta+1))). Both terms
in (14) are O(R^(-e(delta))). Sum over the finitely many i and use the
trivial normalized bound 1 below a fixed R cutoff. This proves (10).
A fixed rational affine normalization preserves (10) by frequency scaling.

Finally, e(delta)<1/6 and tends to 1/6 as delta tends to 1. The digit-side
estimates (1)--(6), including (9/4)L_m<=20m^4, hold for EVERY m>=2.
Guards and packet onset impose no further lower bound on m: their onset
may depend on the fixed word and prefix. The old existential m_* arose
solely from comparing theta_m with a common existential decay exponent.
The new comparison is theta_m<1/6. The function theta_m is decreasing
for m>=2, and the exact integer tests are

$$
(20\cdot48^4)^6>10^{48},\qquad
(20\cdot49^4)^6<10^{49}.
$$

Thus this sufficient parameter test holds exactly for integer m>=49;
it does not assert failure of P1 for m<49. Fix such w,P,d,c and choose
theta_m<alpha<1/6. For each s<d_w, Bowen supplies an ACTUAL group dimension
delta close enough to 1 that e(delta)>alpha and d_w+delta-1>s. Choose
alpha<eta<e(delta) and epsilon=(d_w+delta-1-s)/4. Equations (6)--(9) now
apply with this eta in place of eta_*, and give dimension >s with one
kappa=kappa_mu/Q^2>0 fixed across all digit scales. The same word and
schedule are kept as s tends to d_w; only the group, constants and kappa
may change. This proves the explicit statement at the beginning.
